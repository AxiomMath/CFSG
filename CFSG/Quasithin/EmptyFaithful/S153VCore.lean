module

public import CFSG.Quasithin.EmptyFaithful.ModFA5J
public import CFSG.Quasithin.EmptyFaithful.S153VFin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Split
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCPf

public section

namespace CFSG.Quasithin.ModV

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  CFSG.Quasithin.ModF Equiv

variable {G : Type} [Group G]

abbrev dsub (S K₁ K₂ : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)

end CFSG.Quasithin.ModV

namespace CFSG.Quasithin.ModF

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  CFSG.Quasithin.ModV Equiv

variable {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem pf_eq_one_of_mem_blockQ {L : Subgroup G} (P : AppC.A5Pi L) {e : G} (he : e ∈ blockQ L) :
    P.toPiData.pf e = 1 := by
  have heL : e ∈ L := C1.blockQ_le L he
  rw [P.toPiData.pf_eq (Subgroup.le_normalizer heL), P.hπα e heL]
  have h1 : (⟨e, heL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (AppC.mem_pCore_iff_mem_blockQ _).mpr he
  rw [← P.hαk, MonoidHom.mem_ker] at h1
  rw [h1]
  rfl

omit [Finite G] in
theorem pf_eq_alpha {L : Subgroup G} (P : AppC.A5Pi L) {ℓ : G} (hℓ : ℓ ∈ L) :
    P.toPiData.pf ℓ = ((P.α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  rw [P.toPiData.pf_eq (Subgroup.le_normalizer hℓ), P.hπα ℓ hℓ]

omit [Finite G] in
theorem centralizes_blockU_of_comm_mem {L : Subgroup G} (P : AppC.A5Pi L) {q : G} (hqN : q ∈ Subgroup.normalizer (L : Set G))
    (hq : ∀ k ∈ L, q * k * q⁻¹ * k⁻¹ ∈ blockQ L) : ∀ u ∈ blockU L, q * u * q⁻¹ = u := by
  have hpf1 : P.toPiData.pf q = 1 := by
    refine A5.Delta5.cent_alt _ (fun σ hσ => ?_)
    obtain ⟨k, hk⟩ := P.hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
    have hkσ : P.toPiData.pf (k : G) = σ := by
      rw [pf_eq_alpha P k.2]
      have : (⟨(k : G), k.2⟩ : ↥L) = k := rfl
      rw [this, hk]
    have hkN : (k : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer k.2
    have hqinv : q⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hqN
    have e1 : P.toPiData.pf (q * k * q⁻¹) =
        P.toPiData.pf q * P.toPiData.pf k * (P.toPiData.pf q)⁻¹ := by
      rw [P.toPiData.pf_mul (mul_mem hqN hkN) hqinv, P.toPiData.pf_mul hqN hkN,
        P.toPiData.pf_inv hqN]
    have hmem := hq k k.2
    have e2 : q * k * q⁻¹ = (q * k * q⁻¹ * (k : G)⁻¹) * k := by group
    have hmemN : q * k * q⁻¹ * (k : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.le_normalizer (C1.blockQ_le L hmem)
    have e3 : P.toPiData.pf (q * k * q⁻¹) = P.toPiData.pf k := by
      rw [e2, P.toPiData.pf_mul hmemN hkN, pf_eq_one_of_mem_blockQ P hmem, one_mul]
    rw [e3, hkσ] at e1
    have e4 : P.toPiData.pf q * σ = σ * P.toPiData.pf q := by
      have := e1.symm
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    exact e4
  have hπ : P.π ⟨q, hqN⟩ = 1 := by
    have := P.toPiData.pf_mk ⟨q, hqN⟩
    simpa [hpf1] using this.symm
  exact (P.hker ⟨q, hqN⟩).mp hπ

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

omit [Finite G] in
theorem I_le_normalizer_sup : I ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  rw [c.gen]
  exact sup_le c.S_le_normalizer_sup Subgroup.le_normalizer

omit [Finite G] in
theorem K_le_I : K₁ ⊔ K₂ ≤ I := sup_le c.le₁ c.le₂

omit [Finite G] c in
theorem K_le_centralizer_dsub :
    ∀ x ∈ K₁ ⊔ K₂, ∀ d ∈ dsub S K₁ K₂, x * d = d * x := fun x hx _ hd =>
  Subgroup.mem_centralizer_iff.mp hd.2 x hx

omit [Finite G] in
theorem I_le_normalizer_dsub : I ≤ Subgroup.normalizer ((dsub S K₁ K₂ : Subgroup G) : Set G) := by
  rw [c.gen]
  refine sup_le ?_ ?_
  · intro s hs
    exact C5.mem_normalizer_inf (Subgroup.le_normalizer hs)
      (C5.mem_normalizer_centralizer (c.S_le_normalizer_sup hs))
  · exact Lin2.le_normalizer_of_commute (A := dsub S K₁ K₂) (B := K₁ ⊔ K₂)
      (fun d hd x hx => (K_le_centralizer_dsub x hx d hd).symm)

omit [Finite G] in
theorem dsub_le_pCore : dsub S K₁ K₂ ≤ pCoreOf 2 I :=
  le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans c.sylow.le) c.I_le_normalizer_dsub
    (c.sylow.isPGroup.to_le inf_le_left)

theorem pCoreK_le_pCore : pCoreOf 2 (K₁ ⊔ K₂) ≤ pCoreOf 2 I :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans c.K_le_I)
    (fun _ hg => C1.mem_normalizer_blockQ (c.I_le_normalizer_sup hg)) (pCoreOf_isPGroup 2 _)

theorem Q₀_le_pCoreI : pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ ≤ pCoreOf 2 I := by
  have hQ₂ : IsPGroup 2 (pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ : Subgroup G) :=
    (pCoreOf_isPGroup 2 K₁).to_sup_of_normal_right' (pCoreOf_isPGroup 2 K₂)
      (Lin2.le_normalizer_of_commute (A := pCoreOf 2 K₂) (B := pCoreOf 2 K₁)
        (fun p hp a ha => (c.comm a (pCoreOf_le 2 K₁ ha) p (pCoreOf_le 2 K₂ hp)).symm))
  exact le_pCoreOf_of_le_normalizer 2
    (sup_le ((pCoreOf_le 2 K₁).trans c.le₁) ((pCoreOf_le 2 K₂).trans c.le₂))
    c.I_le_normalizer_Q₀ hQ₂

theorem pCoreK₁_le_pCoreK : pCoreOf 2 K₁ ≤ pCoreOf 2 (K₁ ⊔ K₂) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₁).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 K₁)
      (Lin2.le_normalizer_of_commute (A := pCoreOf 2 K₁) (B := K₂)
        (fun p hp a ha => c.comm p (pCoreOf_le 2 K₁ hp) a ha)))
    (pCoreOf_isPGroup 2 K₁)

theorem pCoreK₂_le_pCoreK : pCoreOf 2 K₂ ≤ pCoreOf 2 (K₁ ⊔ K₂) := by
  have := c.symm.pCoreK₁_le_pCoreK
  rwa [sup_comm] at this

theorem comm_mem_blockU {q : G} (hq : q ∈ pCoreOf 2 I) {k : G} (hk : k ∈ K₁) :
    q * k * q⁻¹ * k⁻¹ ∈ blockU K₁ :=
  C1.commutator_mem_blockU_double c.blk₁.1 c.comm c.le₁ c.I_le_normalizer_sup hq hk

omit [Finite G] in
theorem U₁_le_K₁ : blockU K₁ ≤ K₁ := (C1.blockQ_le K₁).trans' (C1.blockU_le_blockQ c.blk₁.1)

omit [Finite G] in
theorem U₂_le_K₂ : blockU K₂ ≤ K₂ := (C1.blockQ_le K₂).trans' (C1.blockU_le_blockQ c.blk₂.1)

theorem U₁_le_pCoreI : blockU K₁ ≤ pCoreOf 2 I :=
  (C1.blockU_le_blockQ c.blk₁.1).trans (le_sup_left.trans c.Q₀_le_pCoreI)

theorem U₂_le_pCoreI : blockU K₂ ≤ pCoreOf 2 I :=
  (C1.blockU_le_blockQ c.blk₂.1).trans (le_sup_right.trans c.Q₀_le_pCoreI)

theorem Q_centralizes₁ {q : G} (hq : q ∈ pCoreOf 2 I) : ∀ u ∈ blockU K₁, q * u * q⁻¹ = u := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  refine centralizes_blockU_of_comm_mem P
    (c.Q_le_R.trans c.R_le_normalizer₁ hq) ?_
  intro k hk
  exact C1.blockU_le_blockQ c.blk₁.1 (c.comm_mem_blockU hq hk)

theorem exists_split_Q {q : G} (hq : q ∈ pCoreOf 2 I) :
    ∃ d ∈ dsub S K₁ K₂, ∃ u₁ ∈ blockU K₁, ∃ u₂ ∈ blockU K₂, q = d * (u₁ * u₂) := by
  obtain ⟨α₁, hα₁, hαk₁, -⟩ := c.a5₁
  obtain ⟨P₁, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α₁ hα₁ hαk₁
  obtain ⟨α₂, hα₂, hαk₂, -⟩ := c.a5₂
  obtain ⟨P₂, -⟩ := AppC.exists_a5pi c.blk₂.1 c.a5₂ α₂ hα₂ hαk₂
  have hc₁ := c.Q_centralizes₁ hq
  have hc₂ := c.symm.Q_centralizes₁ hq
  have hq₁C : ∀ u ∈ blockU K₁, q * u = u * q := fun u hu => by
    calc q * u = (q * u * q⁻¹) * q := by group
      _ = u * q := by rw [hc₁ u hu]
  have hq₂C : ∀ u ∈ blockU K₂, q * u = u * q := fun u hu => by
    calc q * u = (q * u * q⁻¹) * q := by group
      _ = u * q := by rw [hc₂ u hu]
  obtain ⟨u₁, hu₁, h₁⟩ := AppCS2.exists_split_abs c.blk₁.1 c.a5₁ P₁
    (fun ℓ hℓ => c.comm_mem_blockU hq hℓ) hq₁C
  have hq₁ : u₁ * q ∈ pCoreOf 2 I := mul_mem (c.U₁_le_pCoreI hu₁) hq
  have hq₂C' : ∀ u ∈ blockU K₂, (u₁ * q) * u = u * (u₁ * q) := fun u hu => by
    have h1 : u₁ * u = u * u₁ := c.comm u₁ (c.U₁_le_K₁ hu₁) u (c.U₂_le_K₂ hu)
    calc (u₁ * q) * u = u₁ * (q * u) := by group
      _ = u₁ * (u * q) := by rw [hq₂C u hu]
      _ = (u₁ * u) * q := by group
      _ = (u * u₁) * q := by rw [h1]
      _ = u * (u₁ * q) := by group
  obtain ⟨u₂, hu₂, h₂⟩ := AppCS2.exists_split_abs c.blk₂.1 c.a5₂ P₂
    (fun ℓ hℓ => c.symm.comm_mem_blockU hq₁ hℓ) hq₂C'
  have hq₂ : u₂ * (u₁ * q) ∈ pCoreOf 2 I := mul_mem (c.U₂_le_pCoreI hu₂) hq₁
  have hcent₁ : ∀ x ∈ K₁, x * (u₂ * (u₁ * q)) = (u₂ * (u₁ * q)) * x := fun x hx => by
    have hx2 : x * u₂ = u₂ * x := c.comm x hx u₂ (c.U₂_le_K₂ hu₂)
    calc x * (u₂ * (u₁ * q)) = (x * u₂) * (u₁ * q) := by group
      _ = u₂ * (x * (u₁ * q)) := by rw [hx2]; group
      _ = u₂ * ((u₁ * q) * x) := by rw [h₁ x hx]
      _ = (u₂ * (u₁ * q)) * x := by group
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({u₂ * (u₁ * q)} : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    · rw [Set.mem_singleton_iff.mp hh]
      exact (hcent₁ x hx).symm
    · rw [Set.mem_singleton_iff.mp hh]
      exact (h₂ x hx).symm
  have hqD : u₂ * (u₁ * q) ∈ dsub S K₁ K₂ :=
    ⟨c.sylow.pCoreOf_le hq₂, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mp (hle hx) _ rfl |>.symm⟩
  refine ⟨u₂ * (u₁ * q), hqD, u₁⁻¹, inv_mem hu₁, u₂⁻¹, inv_mem hu₂, ?_⟩
  have e1 : (u₂ * (u₁ * q)) * u₁⁻¹ = u₁⁻¹ * (u₂ * (u₁ * q)) :=
    (hcent₁ u₁⁻¹ (inv_mem (c.U₁_le_K₁ hu₁))).symm
  have e2 : (u₂ * (u₁ * q)) * u₂⁻¹ = u₂⁻¹ * (u₂ * (u₁ * q)) :=
    (h₂ u₂⁻¹ (inv_mem (c.U₂_le_K₂ hu₂))).symm
  calc q = u₁⁻¹ * (u₂⁻¹ * (u₂ * (u₁ * q))) := by group
    _ = u₁⁻¹ * ((u₂ * (u₁ * q)) * u₂⁻¹) := by rw [e2]
    _ = (u₁⁻¹ * (u₂ * (u₁ * q))) * u₂⁻¹ := by group
    _ = ((u₂ * (u₁ * q)) * u₁⁻¹) * u₂⁻¹ := by rw [e1]
    _ = (u₂ * (u₁ * q)) * (u₁⁻¹ * u₂⁻¹) := by group

theorem pCoreOf_eq : pCoreOf 2 I = dsub S K₁ K₂ ⊔ pCoreOf 2 (K₁ ⊔ K₂) := by
  refine le_antisymm (fun q hq => ?_) (sup_le c.dsub_le_pCore c.pCoreK_le_pCore)
  obtain ⟨d, hd, u₁, hu₁, u₂, hu₂, rfl⟩ := c.exists_split_Q hq
  exact mul_mem (Subgroup.mem_sup_left hd) (mul_mem (Subgroup.mem_sup_right
    (c.pCoreK₁_le_pCoreK ((C1.blockU_le_blockQ c.blk₁.1) hu₁)))
    (Subgroup.mem_sup_right (c.pCoreK₂_le_pCoreK ((C1.blockU_le_blockQ c.blk₂.1) hu₂))))

end A5Cfg

end CFSG.Quasithin.ModF
