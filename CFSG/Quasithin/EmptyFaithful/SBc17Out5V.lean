module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem mem_autOn_iff {H V : Subgroup G} {a : MulAut ↥V} :
    a ∈ autOn H V ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ H ∧
      conjAct V ⟨x, hx⟩ = a :=
  CFSG.Quasithin.AutOn.mem_autOn_iff_exists

theorem conjAct_coe {V : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V ⟨x, hx⟩ v : ↥V) : G) = x * v * x⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V _ v

theorem conjAct_conj {V : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G))
    (hxyx : x * y * x⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x, hx⟩ * conjAct V ⟨y, hy⟩ * (conjAct V ⟨x, hx⟩)⁻¹ =
      conjAct V ⟨x * y * x⁻¹, hxyx⟩ := by
  have : (⟨x * y * x⁻¹, hxyx⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

theorem mem_oTwoZIn_iff {L : Subgroup G} {x : G} :
    x ∈ oTwoZIn L ↔ ∃ hx : x ∈ L,
      (QuotientGroup.mk ⟨x, hx⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  unfold oTwoZIn preimageModTwoCore
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, h, rfl⟩

theorem eq_of_forall_mul_inv_mem_center {Γ : Type*} [Group Γ] (hperf : commutator Γ = ⊤)
    (ψ : MulAut Γ) (hz : ∀ a : Γ, a * (ψ a)⁻¹ ∈ Subgroup.center Γ) (a : Γ) : ψ a = a := by
  let z : Γ →* Γ :=
    { toFun := fun a => a * (ψ a)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_center_iff.mp (hz b)
        have ha := Subgroup.mem_center_iff.mp (hz a)
        simp only [map_mul, mul_inv_rev]
        calc a * b * ((ψ b)⁻¹ * (ψ a)⁻¹) = a * (b * (ψ b)⁻¹) * (ψ a)⁻¹ := by group
          _ = (b * (ψ b)⁻¹) * a * (ψ a)⁻¹ := by rw [hb a]
          _ = (b * (ψ b)⁻¹) * (a * (ψ a)⁻¹) := by group
          _ = (a * (ψ a)⁻¹) * (b * (ψ b)⁻¹) := ha _ }
  have hzdef : ∀ a, z a = a * (ψ a)⁻¹ := fun _ => rfl
  have hker : (⊤ : Subgroup Γ) ≤ z.ker := by
    rw [← hperf, commutator_def Γ]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have hc : z g₁ * z g₂ = z g₂ * z g₁ := (Subgroup.mem_center_iff.mp (hz g₁) (z g₂)).symm
    rw [hc]
    group
  have h1 := hker (Subgroup.mem_top a)
  rw [MonoidHom.mem_ker, hzdef, mul_inv_eq_one] at h1
  exact h1.symm

theorem mem_innerSub_of_autOn_out5 {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hD : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn L)
    (hS : Out5Inner ↥(autOn L V)) {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hk5 : k ^ 5 = 1) : k ∈ innerSub L := by
  set S := autOn L V with hSdef
  have hSn : ∀ (y : G) (hyN : y ∈ Subgroup.normalizer (L : Set G))
      (hyV : y ∈ Subgroup.normalizer (V : Set G)), ∀ s ∈ S,
      conjAct V ⟨y, hyV⟩ * s * (conjAct V ⟨y, hyV⟩)⁻¹ ∈ S := by
    intro y hyN hyV s hs
    obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn_iff.mp hs
    have hyx : y * x * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN x).mp hxL
    have hyxN : y * x * y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      mul_mem (mul_mem hyV hx) (inv_mem hyV)
    rw [conjAct_conj hyV hx hyxN]
    exact mem_autOn_iff.mpr ⟨_, hyxN, hyx, rfl⟩
  set κ : MulAut ↥V := conjAct V ⟨k, hkV⟩ with hκ
  have hκS : κ ∈ Subgroup.normalizer (S : Set (MulAut ↥V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSn k hk hkV s hs, fun hs => ?_⟩
    have h1 := hSn k⁻¹ (inv_mem hk) (inv_mem hkV) _ hs
    have h2 : conjAct V ⟨k⁻¹, inv_mem hkV⟩ = κ⁻¹ := by
      have : (⟨k⁻¹, inv_mem hkV⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨k, hkV⟩⁻¹ := rfl
      rw [this, map_inv]
    rw [h2] at h1
    simpa [mul_assoc] using h1
  set φ : MulAut ↥S := Subgroup.normalizerMonoidHom S ⟨κ, hκS⟩ with hφ
  have hφapp : ∀ s : ↥S, ((φ s : ↥S) : MulAut ↥V) = κ * s * κ⁻¹ := fun s =>
    Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨κ, hκS⟩ s
  have hφ5 : φ ^ 5 = 1 := by
    rw [hφ, ← map_pow]
    have h5 : (⟨κ, hκS⟩ : Subgroup.normalizer (S : Set (MulAut ↥V))) ^ 5 = 1 := by
      apply Subtype.ext
      show κ ^ 5 = 1
      rw [hκ, ← map_pow]
      have : (⟨k, hkV⟩ : Subgroup.normalizer (V : Set G)) ^ 5 = 1 := Subtype.ext hk5
      rw [this, map_one]
    rw [h5, map_one]
  obtain ⟨g, hg⟩ := hS φ hφ5
  obtain ⟨x₀, hx₀N, hx₀L, hx₀⟩ := mem_autOn_iff.mp g.2
  set c : G := x₀⁻¹ * k with hc
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hx₀L)) hk
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := mul_mem (inv_mem hx₀N) hkV
  have hcomm : ∀ s ∈ S, conjAct V ⟨c, hcV⟩ * s = s * conjAct V ⟨c, hcV⟩ := by
    intro s hs
    have h1 : κ * s * κ⁻¹ = (g : MulAut ↥V) * s * (g : MulAut ↥V)⁻¹ := by
      have h2 := congrArg (fun t : ↥S => (t : MulAut ↥V)) (hg ⟨s, hs⟩)
      simpa [hφapp] using h2
    have h3 : conjAct V ⟨c, hcV⟩ = (g : MulAut ↥V)⁻¹ * κ := by
      have : (⟨c, hcV⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨x₀, hx₀N⟩⁻¹ * ⟨k, hkV⟩ := rfl
      rw [this, map_mul, map_inv, hx₀]
    rw [h3]
    calc (g : MulAut ↥V)⁻¹ * κ * s = (g : MulAut ↥V)⁻¹ * (κ * s * κ⁻¹) * κ := by group
      _ = (g : MulAut ↥V)⁻¹ * ((g : MulAut ↥V) * s * (g : MulAut ↥V)⁻¹) * κ := by rw [h1]
      _ = s * ((g : MulAut ↥V)⁻¹ * κ) := by group
  have hxc : ∀ x ∈ L, ⁅x, c⁆ ∈ oTwoZIn L := by
    intro x hx
    have hxN := hLV hx
    have hwN : ⁅x, c⁆ ∈ Subgroup.normalizer (V : Set G) := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxN hcV) (inv_mem hxN)) (inv_mem hcV)
    apply hD
    refine ⟨?_, ?_⟩
    · have h1 : c * x⁻¹ * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (inv_mem hx)
      have e : ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hx h1
    · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hcm := hcomm (conjAct V ⟨x, hxN⟩) (mem_autOn_iff.mpr ⟨x, hxN, hx, rfl⟩)
      have hw : conjAct V ⟨⁅x, c⁆, hwN⟩ = 1 := by
        have e : (⟨⁅x, c⁆, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨x, hxN⟩ * ⟨c, hcV⟩ * ⟨x, hxN⟩⁻¹ * ⟨c, hcV⟩⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcm]
        group
      have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) hw
      simp only [conjAct_coe, MulAut.one_apply] at h1
      calc v * ⁅x, c⁆ = (⁅x, c⁆ * v * ⁅x, c⁆⁻¹) * ⁅x, c⁆ := by rw [h1]
        _ = ⁅x, c⁆ * v := by group
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker = CFSG.pCore 2 ↥L :=
    QuotientGroup.ker_mk' _
  obtain ⟨ψ, hψ⟩ := exists_mulAut_comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩)
    (map_normalizerMonoidHom_eq_one_iff hker hcN)
  have hcoe : ∀ x : ↥L, ((x * (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ x)⁻¹ : ↥L) : G) = ⁅(x : G), c⁆ := by
    intro x
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom, commutatorElement_def]
    group
  have hz : ∀ a : ↥L ⧸ CFSG.pCore 2 ↥L, a * (ψ a)⁻¹ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro a
    induction a using QuotientGroup.induction_on with | H x => ?_
    have h1 : ψ (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ x) :=
      hψ x
    rw [h1, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    obtain ⟨hmem, hcen⟩ := mem_oTwoZIn_iff.mp (hxc x x.2)
    convert hcen using 2
    apply Subtype.ext
    exact hcoe x
  have hψ1 := eq_of_forall_mul_inv_mem_center hq.1.commutator_eq_top ψ hz
  have hcM : c ∈ cMod L := by
    refine mem_cMod.mpr ⟨hcN, fun x hx => ?_⟩
    have h1 : ψ (QuotientGroup.mk (⟨x, hx⟩ : ↥L)) =
        QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ ⟨x, hx⟩) := hψ ⟨x, hx⟩
    rw [hψ1] at h1
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (⟨x, hx⟩ * (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ ⟨x, hx⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      show (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) *
        (QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ ⟨x, hx⟩))⁻¹ = 1
      rw [← h1, mul_inv_cancel]
    have h3 := (map_eq_one_iff_mem_pCoreOf hker _).mp h2
    rwa [hcoe] at h3
  exact mem_innerSub_iff.mpr ⟨x₀, hx₀L, c, hcM, by rw [hc]; group⟩

end SBc17

end CFSG.Quasithin
