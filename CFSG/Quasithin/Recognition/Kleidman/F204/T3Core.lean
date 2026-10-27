module

public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase2
public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Rep

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section NN

variable {H M B T : Subgroup G} (hA : Amal H M B T)
include hA

def NN (α : Geo H M) : Subgroup G where
  carrier := {g | g ∈ stab α ∧ ∀ δ ∈ nbrs α, ∀ z ∈ Zv δ, ⁅z, g⁆ ∈ Zv α}
  mul_mem' := by
    rintro g g' ⟨hg, hgZ⟩ ⟨hg', hg'Z⟩
    refine ⟨(stab α).mul_mem hg hg', fun δ hδ z hz => ?_⟩
    have e : ⁅z, g * g'⁆ = ⁅z, g⁆ * (g * ⁅z, g'⁆ * g⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine (Zv α).mul_mem (hgZ δ hδ z hz) ?_
    exact (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv α hg) _).mp (hg'Z δ hδ z hz)
  one_mem' := ⟨(stab α).one_mem, fun δ hδ z hz => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro g ⟨hg, hgZ⟩
    refine ⟨(stab α).inv_mem hg, fun δ hδ z hz => ?_⟩
    have e : ⁅z, g⁻¹⁆ = g⁻¹ * ⁅z, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv α ((stab α).inv_mem hg)) _).mp
      ((Zv α).inv_mem (hgZ δ hδ z hz))

theorem mem_NN {α : Geo H M} {n : G} :
    n ∈ NN hA α ↔ n ∈ stab α ∧ ∀ δ ∈ nbrs α, ∀ z ∈ Zv δ, ⁅z, n⁆ ∈ Zv α := Iff.rfl

theorem NN_normal (α : Geo H M) {n g : G} (hn : n ∈ NN hA α) (hg : g ∈ stab α) :
    g * n * g⁻¹ ∈ NN hA α := by
  obtain ⟨hnα, hnZ⟩ := hn
  refine ⟨(stab α).mul_mem ((stab α).mul_mem hg hnα) ((stab α).inv_mem hg), fun δ hδ z hz => ?_⟩
  set g' : ↥(H ⊔ M) := ⟨g, mem_stab.mp hg |>.1⟩ with hg'
  have hgα : g' • α = α := smul_eq_of_mem_stab hg
  have hδ' : g'⁻¹ • δ ∈ nbrs α := by
    have := (smul_adj g'⁻¹).mpr (show (graph (H ⊔ M) H M).Adj α δ from hδ)
    rwa [show g'⁻¹ • α = α from by rw [inv_smul_eq_iff]; exact hgα.symm] at this
  have hz' : g⁻¹ * z * g ∈ Zv (g'⁻¹ • δ) := by
    rw [Zv_smul, mem_conjSub]
    have e : (((g'⁻¹ : ↥(H ⊔ M)) : G)) = g⁻¹ := rfl
    rw [e]
    have e2 : g⁻¹⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [e2]
    exact hz
  have h1 := hnZ _ hδ' _ hz'
  have e : ⁅z, g * n * g⁻¹⁆ = g * ⁅g⁻¹ * z * g, n⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv α hg) _).mp h1


theorem Zv_le_NN (α α' ε : Geo H M) (hε1 : ∀ δ ∈ nbrs α, Zv δ ≤ Qv ε)
    (hε2 : ∀ q ∈ Qv ε, ∃ a ∈ Zv α, ∃ u ∈ Qv α', q = a * u) (hs : Zv α' ≤ stab α) :
    Zv α' ≤ NN hA α := by
  intro a ha
  refine ⟨hs ha, fun δ hδ z hz => ?_⟩
  obtain ⟨a₀, ha₀, u, hu, hzau⟩ := hε2 z (hε1 δ hδ hz)
  have hua : u * a = a * u :=
    Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α' ha).2 u hu
  have e : ⁅z, a⁆ = a₀ * (a * a₀⁻¹ * a⁻¹) := by
    rw [hzau]
    simp only [commutatorElement_def]
    calc a₀ * u * a * (a₀ * u)⁻¹ * a⁻¹ = a₀ * (u * a) * u⁻¹ * a₀⁻¹ * a⁻¹ := by group
      _ = a₀ * (a * u) * u⁻¹ * a₀⁻¹ * a⁻¹ := by rw [hua]
      _ = a₀ * (a * a₀⁻¹ * a⁻¹) := by group
  rw [e]
  exact (Zv α).mul_mem ha₀
    ((Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv α (hs ha)) _).mp
      ((Zv α).inv_mem ha₀))

end NN

section Big

variable {H M : Subgroup G}

theorem three_mem_of_big {α : Geo H M} {N : Subgroup G} (hNs : N ≤ stab α)
    (hNn : ∀ n ∈ N, ∀ g ∈ stab α, g * n * g⁻¹ ∈ N)
    (hbig : ∀ g ∈ stab α, ∃ n ∈ N, n⁻¹ * g ∈ Qv α) {r : G} (hr : r ∈ stab α) (hr3 : r ^ 3 = 1) :
    r ∈ N := by
  have hN' : (N.subgroupOf (stab α)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn _ hn g g.2⟩
  set ψ : ↥(stab α) →* ↥(stab α) ⧸ N.subgroupOf (stab α) := QuotientGroup.mk' _ with hψ
  have hψ1 : ∀ x : ↥(stab α), ψ x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; rfl
  obtain ⟨n, hn, hq⟩ := hbig r hr
  have hqs : n⁻¹ * r ∈ stab α := pCoreOf_le 2 (stab α) hq
  have hns : n ∈ stab α := hNs hn
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (stab α) ⟨n⁻¹ * r, hq⟩
  have hk' : (n⁻¹ * r) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set r' : ↥(stab α) := ⟨r, hr⟩
  set q' : ↥(stab α) := ⟨n⁻¹ * r, hqs⟩
  set n' : ↥(stab α) := ⟨n, hns⟩
  have hrq : r' = n' * q' := Subtype.ext (by simp [r', n', q'])
  have hψn : ψ n' = 1 := (hψ1 n').mpr hn
  have hψr : ψ r' = ψ q' := by rw [hrq, map_mul, hψn, one_mul]
  have h3 : (ψ r') ^ 3 = 1 := by
    rw [← map_pow]
    have : r' ^ 3 = 1 := Subtype.ext (by simpa using hr3)
    rw [this, map_one]
  have h2 : (ψ r') ^ 2 ^ k = 1 := by
    rw [hψr, ← map_pow]
    have : q' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rw [hg, pow_one] at this
  exact (hψ1 r').mp this


variable {H M : Subgroup G}

theorem trans_of_big {α : Geo H M} {N : Subgroup G} (hNs : N ≤ stab α)
    (hbig : ∀ g ∈ stab α, ∃ n ∈ N, n⁻¹ * g ∈ Qv α) {B T : Subgroup G} (hA : Amal H M B T)
    {δ δ' : Geo H M} (hδ : δ ∈ nbrs α) (hδ' : δ' ∈ nbrs α) :
    ∃ e : ↥(H ⊔ M), (e : G) ∈ N ∧ e • δ = δ' := by
  obtain ⟨g, hg, hgδ⟩ := stab_transitive_on_nbrs hδ hδ'
  obtain ⟨n, hn, hq⟩ := hbig g hg
  have hnα : n ∈ stab α := hNs hn
  have hqδ : n⁻¹ * g ∈ stab δ := hA.Qv_le_stab_of_mem_nbrs hδ hq
  set e : ↥(H ⊔ M) := ⟨n, (mem_stab.mp hnα).1⟩ with he
  refine ⟨e, hn, ?_⟩
  have hq' : (⟨n⁻¹ * g, (mem_stab.mp (pCoreOf_le 2 (stab α) hq)).1⟩ : ↥(H ⊔ M)) • δ = δ :=
    smul_eq_of_mem_stab hqδ
  have : g = e * ⟨n⁻¹ * g, (mem_stab.mp (pCoreOf_le 2 (stab α) hq)).1⟩ := by
    apply Subtype.ext; simp [he]
  rw [← hgδ, this, mul_smul, hq']


end Big

section A5

variable (F : Frame L1 L2 S D X)
include F

theorem exists_mul_Q_of_normal {α : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = true)
    {N : Subgroup G} (hNs : N ≤ stab α) (hNn : ∀ n ∈ N, ∀ g ∈ stab α, g * n * g⁻¹ ∈ N)
    (hNQ : ¬ N ≤ Qv α) : ∀ g ∈ stab α, ∃ n ∈ N, n⁻¹ * g ∈ Qv α := by
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hα
  have hN' : (N.subgroupOf (stab α)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn _ hn g g.2⟩
  have : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
  have hmapn : ((N.subgroupOf (stab α)).map φ).Normal := Subgroup.Normal.map hN' φ hφs
  have htop : (N.subgroupOf (stab α)).map φ = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((N.subgroupOf (stab α)).map φ) with hb | ht
    · exfalso
      obtain ⟨a, haN, haQ⟩ : ∃ a ∈ N, a ∉ Qv α := by
        rw [IsConcreteLE.not_le_iff_exists] at hNQ
        exact hNQ
      have hmem : φ ⟨a, hNs haN⟩ ∈ (N.subgroupOf (stab α)).map φ :=
        ⟨⟨a, hNs haN⟩, Subgroup.mem_subgroupOf.mpr haN, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      have : (⟨a, hNs haN⟩ : ↥(stab α)) ∈ φ.ker := MonoidHom.mem_ker.mpr hmem
      rw [hφk] at this
      exact haQ (Subgroup.mem_subgroupOf.mp this)
    · exact ht
  intro g hg
  have hmem : φ ⟨g, hg⟩ ∈ (N.subgroupOf (stab α)).map φ := by rw [htop]; trivial
  obtain ⟨n', hn', hφn⟩ := hmem
  refine ⟨(n' : G), Subgroup.mem_subgroupOf.mp hn', ?_⟩
  have : n'⁻¹ * ⟨g, hg⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφn]; group
  rw [hφk] at this
  exact Subgroup.mem_subgroupOf.mp this

end A5

end CFSG.Quasithin.Kleidman.F204
