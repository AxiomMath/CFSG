module

public import CFSG.Quasithin.EmptyFaithful.S151TBDef

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjAct_eq_one_iff (V : Subgroup G) (n : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V n = 1 ↔ (n : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff n

theorem pCore_le_centralizer {L R V : Subgroup G} (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (h1 : pCoreOf 2 (L ⊔ R) ≤ (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have hnorm : L ⊔ R ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 L) (hRL.trans (normalizer_le_normalizer_pCoreOf 2 L))
  have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hnorm (pCoreOf_isPGroup 2 L)
  exact (h1 (hle hx)).2

theorem mk_mem_center_of_centralizer {L R V : Subgroup G}
    (hC : (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ R) ⊔ oTwoZIn L)
    {x : ↥L} (hx : (x : G) ∈ Subgroup.centralizer (V : Set G)) :
    (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L) := by
  have hLLR : L ≤ L ⊔ R := le_sup_left
  have hxLR : (x : G) ∈ (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := ⟨hLLR x.2, hx⟩
  have hx1 := hC hxLR
  set P := pCoreOf 2 (L ⊔ R) with hPdef
  have hPN : L ⊔ R ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 (L ⊔ R)
  have hZL : oTwoZIn L ≤ Subgroup.normalizer (P : Set G) := fun y hy => hPN (by
    obtain ⟨z, -, rfl⟩ := hy
    exact hLLR z.2)
  have hmul : ((P ⊔ oTwoZIn L : Subgroup G) : Set G) = (P : Set G) * (oTwoZIn L : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P (oTwoZIn L) hZL
  have hx2 : (x : G) ∈ (P : Set G) * (oTwoZIn L : Set G) := by
    rw [← hmul]
    exact hx1
  obtain ⟨a, ha, b, hb, hab⟩ := hx2
  have hbL : b ∈ L := by
    obtain ⟨z, -, rfl⟩ := hb
    exact z.2
  have haL : a ∈ L := by
    have : a = (x : G) * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact L.mul_mem x.2 (L.inv_mem hbL)
  have hPL : P ⊓ L ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 (L ⊔ R)).to_le inf_le_left)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hU' := Subgroup.mem_normalizer_iff.1 (hPN (hLLR hl)) y
    have hL' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) y
    simp only [Subgroup.mem_inf] at hU' hL' ⊢
    exact and_congr hU' hL'
  have ha2 : a ∈ pCoreOf 2 L := hPL ⟨ha, haL⟩
  obtain ⟨y, hy, rfl⟩ := ha2
  obtain ⟨z, hz, hzb⟩ := hb
  have hxeq : x = y * z := by
    apply Subtype.ext
    rw [← hab, ← hzb]
    rfl
  rw [hxeq, QuotientGroup.mk_mul]
  have hy' : y ∈ CFSG.pCore 2 ↥L := by
    exact hy
  have hy1 : (QuotientGroup.mk y : LStar L) = 1 := (QuotientGroup.eq_one_iff y).2 hy'
  rw [hy1, one_mul]
  exact hz

theorem exists_epi_autOn {L R V : Subgroup G} (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (h1 : pCoreOf 2 (L ⊔ R) ≤ (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
      (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ R) ⊔ oTwoZIn L ∧
      IsTwoReducedIn (L ⊔ R) V) :
    ∃ ψ : ↥L →* ↥(autOn L V), Function.Surjective ψ ∧ CFSG.pCore 2 ↥L ≤ ψ.ker ∧
      ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L) := by
  obtain ⟨hP, hC, hred⟩ := h1
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  let ψ0 : ↥L →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hLN)
  have hmem : ∀ x : ↥L, ψ0 x ∈ autOn L V := fun x =>
    ⟨Subgroup.inclusion hLN x, x.2, rfl⟩
  let ψ : ↥L →* ↥(autOn L V) := ψ0.codRestrict (autOn L V) hmem
  have hψ0 : ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro x
    have h := conjAct_eq_one_iff V (Subgroup.inclusion hLN x)
    exact ⟨fun h' => h.1 (congrArg Subtype.val h'), fun h' => Subtype.ext (h.2 h')⟩
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rintro ⟨y, n, hn, rfl⟩
    exact ⟨⟨n.1, hn⟩, by
      apply Subtype.ext
      rfl⟩
  · intro x hx
    rw [MonoidHom.mem_ker, hψ0]
    have hx' : (x : G) ∈ pCoreOf 2 L := ⟨x, by assumption, rfl⟩
    exact pCore_le_centralizer hRL hP hx'
  · intro x hx
    rw [hψ0] at hx
    exact mk_mem_center_of_centralizer hC hx

end CFSG.Quasithin.S151TB
