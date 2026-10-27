module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CBridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CPar
public import CFSG.Quasithin.EmptyFaithful.FLc3Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

noncomputable abbrev kS (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Subgroup G :=
  kI T Mc M B₀ ⊔ sOf152 T Mc M B₀

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem kS_le_centralizer :
    kS T Mc M B₀ ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) :=
  sup_le (kI_le_centralizer T Mc M B₀) d.c.S_le_centralizer

theorem kS_le_I : kS T Mc M B₀ ≤ I :=
  sup_le (d.kI_le_X.trans d.c.X_le_I) (S_le_I152 d.c.inputs)

theorem sylow_kS : IsSylowTwoOf (sOf152 T Mc M B₀) (kS T Mc M B₀) :=
  A4.isSylowTwoOf_mono d.c.sylow le_sup_right d.kS_le_I

theorem mZ_eq : mZ1516 (kS T Mc M B₀) (zSOf T Mc M B₀) = kS T Mc M B₀ :=
  inf_eq_right.2 d.kS_le_centralizer

theorem q1_eq : q1_1516 (kS T Mc M B₀) (zSOf T Mc M B₀) = pCoreOf 2 (kS T Mc M B₀) := by
  unfold q1_1516
  rw [d.mZ_eq]

theorem facts15128 (hF : ¬ X ≤ Mc) :
    Facts15128 T (kS T Mc M B₀) (zSOf T Mc M B₀) (zSOf T Mc M B₀) X := by
  have hD := d.c.inputs
  obtain ⟨hU, hred⟩ := d.isTwoReduced_W
  have hSN := d.S_le_normalizer_X
  have hS2 : IsPGroup 2 (sOf152 T Mc M B₀) :=
    d.c.setting.qtfe.sylow.1.to_le S_le_T152
  have hLU : X ≤ Subgroup.normalizer (uOf1527 (zSOf T Mc M B₀) X : Set G) :=
    le_normalizer_conjClosure _ X
  have hZU : zSOf T Mc M B₀ ≤ uOf1527 (zSOf T Mc M B₀) X := le_conjClosure _ X
  have hULU : uLOf1527 (zSOf T Mc M B₀) X ≤ uOf1527 (zSOf T Mc M B₀) X := by
    unfold uLOf1527
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : l * u⁻¹ * l⁻¹ ∈ uOf1527 (zSOf T Mc M B₀) X :=
      (Subgroup.mem_normalizer_iff.1 (hLU hl) u⁻¹).1 ((uOf1527 (zSOf T Mc M B₀) X).inv_mem hu)
    have : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact (uOf1527 (zSOf T Mc M B₀) X).mul_mem hu h1
  have hUc : ∀ a ∈ uOf1527 (zSOf T Mc M B₀) X, ∀ b ∈ uOf1527 (zSOf T Mc M B₀) X,
      a * b = b * a := fun a ha b hb => by
    have := hU.1
    exact setLike_mul_comm ha hb
  have hU2 : ∀ a ∈ uOf1527 (zSOf T Mc M B₀) X, a ^ 2 = 1 := hU.2
  have hSZ : ∀ s ∈ s1516 T (zSOf T Mc M B₀), ∀ z ∈ zSOf T Mc M B₀, s * z * s⁻¹ = z := by
    intro s hs z hz
    have h1 := Subgroup.mem_centralizer_iff.1 hs.2 z hz
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [← h1]
      _ = z := by group
  have hodd : Odd (((s1516 T (zSOf T Mc M B₀)) ⊓ X).relIndex X) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp d.f.sylow.2.2)
  have hd := FLc.ud_decomp hLU hUc hU2 hodd hZU
    (fun s hs z hz => hSZ s ⟨hs.1.1, hs.1.2⟩ z hz)
  have hcz := FLc.centralizer_zU_eq hd hZU hULU
  have hkSle := d.kS_le_centralizer
  refine ⟨hU, hLU, hZU, hULU, inf_le_right,
    fun s hs l hl => (Subgroup.mem_normalizer_iff.1 (hSN hs) l).1 hl, hSZ, hS2, ?_, ?_, ?_, ?_,
    d.f.sylow, ?_, hd⟩
  ·
    rw [d.q1_eq]
    exact pCoreOf_le_of_isSylowTwoOf d.sylow_kS
  ·
    intro m hm q hq
    rw [d.q1_eq] at hq ⊢
    rw [d.mZ_eq] at hm
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hm.1) q).1 hq
  ·
    intro s hs z hz
    have hz' : z ∈ zSOf T Mc M B₀ ⊔
        (uOf1527 (zSOf T Mc M B₀) X ⊓ Subgroup.centralizer (X : Set G)) := hz.1
    have hle : zSOf T Mc M B₀ ⊔
        (uOf1527 (zSOf T Mc M B₀) X ⊓ Subgroup.centralizer (X : Set G)) ≤
        Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun c hc' => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hSZ s hs.1 w hw
        calc w * s = (s * w * s⁻¹) * s := by rw [this]
          _ = s * w := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hc'.2 s hs.2).symm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hz')
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [this]
      _ = z := by group
  ·
    intro l hl hfix
    have hcent : l ∈ Subgroup.centralizer
        (FLc.projZU (zSOf T Mc M B₀) X (uOf1527 (zSOf T Mc M B₀) X) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have := hfix z hz
      calc z * l = (l * z * l⁻¹) * l := by rw [this]
        _ = l * z := by group
    have h2 : l ∈ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := (hcz l hl).2 hcent
    have h3 := d.inf_centralizer_le_kI_sup ⟨hl, h2⟩
    refine ⟨?_, hl⟩
    rw [d.mZ_eq]
    have h4 : kI T Mc M B₀ ⊔ (sOf152 T Mc M B₀ ⊓ X) ≤ kS T Mc M B₀ :=
      sup_le_sup_left inf_le_left _
    exact h4 h3
  ·
    intro h
    apply hF
    have hXle : X ≤ kS T Mc M B₀ := by
      intro x hx
      have : x ∈ mZ1516 (kS T Mc M B₀) (zSOf T Mc M B₀) ⊓ X := by rw [h]; exact hx
      rw [d.mZ_eq] at this
      exact this.1
    intro x hx
    exact (centralizer_zS_le_inf152 hD (hkSle (hXle hx))).1

end CData

end C

end S15223P4

end CFSG.Quasithin
