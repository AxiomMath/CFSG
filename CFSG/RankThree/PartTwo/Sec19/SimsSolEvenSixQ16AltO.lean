module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16AltFix
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixLen2
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Mod
public import CFSG.Quasithin.H13.J4Order
public import CFSG.CGT.A8S.N0EnumInputs
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.CGT.PushingUpLit.SolK.CaseII
public import CFSG.CGT.PushingUpLit.SolK.Final
public import CFSG.CGT.PushingUpLit.SolK.GenFourA8
public import CFSG.CGT.PushingUpLit.SolK.GenFourPSp
public import CFSG.CGT.PushingUpLit.SolK.HighN
public import CFSG.CGT.PushingUpLit.SolK.SevenTwo
public import CFSG.CGT.PushingUpLit.SolKMT.Statement
public import CFSG.GF2Type.Smith1979CharTwo
public import CFSG.LargeExtraspecial.DWModelSplit
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.G23Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixAlt
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixST

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Q16Alt

namespace Lemma5

@[instance_reducible] private def permBarACG (n : ℕ) : AddCommGroup (permBar n) :=
  { (inferInstance : AddGroup (permBar n)) with
    add_comm := fun x y => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm] }

local notation "V₀" => klein4 ({4, 5} : Finset (Fin 6))ᶜ

theorem b1_mem_V0 : b1 ∈ V₀ := mem_klein4_45_iff.2 (Or.inr (Or.inl rfl))

theorem b2_mem_V0 : b2 ∈ V₀ := mem_klein4_45_iff.2 (Or.inr (Or.inr (Or.inl rfl)))

theorem commute_four {K : Type*} [Group K] {a b : K} (h : Commute a b) {σ τ : K}
    (hσ : σ = 1 ∨ σ = a ∨ σ = b ∨ σ = a * b) (hτ : τ = 1 ∨ τ = a ∨ τ = b ∨ τ = a * b) :
    Commute σ τ := by
  have h' : Commute b a := h.symm
  rcases hσ with hσ | hσ | hσ | hσ <;> rcases hτ with hτ | hτ | hτ | hτ <;> rw [hσ, hτ]
  all_goals first
    | exact Commute.one_left _
    | exact Commute.one_right _
    | exact Commute.refl _
    | exact h
    | exact h'
    | exact (Commute.refl _).mul_right h
    | exact h'.mul_right (Commute.refl _)
    | exact (Commute.refl _).mul_left h'
    | exact h.mul_left (Commute.refl _)

theorem V0_comm {σ τ : Perm (Fin 6)} (hσ : σ ∈ V₀) (hτ : τ ∈ V₀) : σ * τ = τ * σ :=
  commute_four (b1_mul_b2 : Commute b1 b2) (mem_klein4_45_iff.1 hσ) (mem_klein4_45_iff.1 hτ)

theorem card_V0 : Nat.card ↥V₀ = 4 := card_klein4 (by decide)

def Zs : AddSubgroup (permBar 6) where
  carrier := {v | v = 0 ∨ v = zBar}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (add_zero _)
    · exact Or.inr (zero_add _)
    · exact Or.inr (add_zero _)
    · exact Or.inl (permBar_add_self _)
  neg_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl neg_zero
    · exact Or.inr (permBar_neg_eq _)

theorem mem_Zs {v : permBar 6} : v ∈ Zs ↔ v = 0 ∨ v = zBar := Iff.rfl

section Core

variable {Γ : Type} [Group Γ]

structure PiLike (θ : Γ →* Perm (Fin 6)) (p : Γ → permBar 6) : Prop where
  mul : ∀ a b, θ a = 1 → θ b = 1 → p (a * b) = p a + p b
  conj : ∀ m q, θ q = 1 → p (m * q * m⁻¹) = barAct (θ m) (p q)
  inj : ∀ a b, θ a = 1 → θ b = 1 → p a = p b → a = b
  surj : ∀ u : altHeart 6, ∃ q, θ q = 1 ∧ p q = heartToBar u

structure OData (θ : Γ →* Perm (Fin 6)) (p : Γ → permBar 6) (z : Γ) (O : Subgroup Γ) : Prop where
  pi : PiLike θ p
  card_ker : Nat.card θ.ker = 16
  theta_z : θ z = 1
  p_z : p z = zBar
  map_O : O.map θ = V₀
  not_le : ¬ θ.ker ≤ O
  norm_ker : ∀ q, θ q = 1 → ∀ o ∈ O, q * o * q⁻¹ ∈ O
  norm_cent : ∀ y, y * z = z * y → ∀ o ∈ O, y * o * y⁻¹ ∈ O
  exists_c3 : ∃ y, y * z = z * y ∧ θ y = c3

variable [Finite Γ]

namespace OData

variable {θ : Γ →* Perm (Fin 6)} {p : Γ → permBar 6} {z : Γ} {O : Subgroup Γ}
  (H : OData θ p z O)
include H

theorem p_one : p 1 = 0 := by
  have h := H.pi.mul 1 1 (map_one θ) (map_one θ)
  rw [mul_one] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem p_inv {a : Γ} (ha : θ a = 1) : p a⁻¹ = p a := by
  have h := H.pi.mul a a⁻¹ ha (by rw [map_inv, ha, inv_one])
  rw [mul_inv_cancel, H.p_one] at h
  have h' : p a⁻¹ = -p a := eq_neg_of_add_eq_zero_right h.symm
  rw [h', permBar_neg_eq]

theorem mem_V0 {x : Γ} (hx : x ∈ O) : θ x ∈ V₀ := by
  rw [← H.map_O]
  exact Subgroup.mem_map_of_mem θ hx

theorem exists_lift {σ : Perm (Fin 6)} (hσ : σ ∈ V₀) : ∃ o ∈ O, θ o = σ := by
  rw [← H.map_O] at hσ
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hσ
  exact ⟨o, ho, rfl⟩

theorem theta_comm {x y : Γ} (hx : x ∈ O) (hy : y ∈ O) : θ (x * y * x⁻¹ * y⁻¹) = 1 := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, V0_comm (H.mem_V0 hx) (H.mem_V0 hy)]
  group

theorem comm_mem {x y : Γ} (hx : x ∈ O) (hy : y ∈ O) : x * y * x⁻¹ * y⁻¹ ∈ O :=
  O.mul_mem (O.mul_mem (O.mul_mem hx hy) (O.inv_mem hx)) (O.inv_mem hy)

theorem conj_comm_mem {o q : Γ} (ho : o ∈ O) (hq : θ q = 1) :
    o * q * o⁻¹ * q⁻¹ ∈ O ∧ θ (o * q * o⁻¹ * q⁻¹) = 1 := by
  refine ⟨?_, ?_⟩
  · have h := H.norm_ker q hq o⁻¹ (O.inv_mem ho)
    have e : o * q * o⁻¹ * q⁻¹ = o * (q * o⁻¹ * q⁻¹) := by group
    rw [e]
    exact O.mul_mem ho h
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hq]
    group

theorem p_conj_comm {o q : Γ} (hq : θ q = 1) :
    p (o * q * o⁻¹ * q⁻¹) = barAct (θ o) (p q) - p q := by
  have h1 : θ (o * q * o⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hq]
    group
  have h2 : θ q⁻¹ = 1 := by rw [map_inv, hq, inv_one]
  rw [H.pi.mul _ _ h1 h2, H.pi.conj o q hq, H.p_inv hq, permBar_sub_eq_add]

theorem exists_of_mem_zPerp {w : permBar 6} (hw : w ∈ zPerp) :
    ∃ x ∈ O, θ x = 1 ∧ p x = w := by
  obtain ⟨σ, hσ, u, hu, rfl⟩ := exists_eq_sub_of_mem_zPerp hw
  obtain ⟨o, ho, rfl⟩ := H.exists_lift hσ
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨q, hq, hpq⟩ := H.pi.surj u'
  obtain ⟨hO, h1⟩ := H.conj_comm_mem ho hq
  exact ⟨_, hO, h1, by rw [H.p_conj_comm hq, hpq]⟩

theorem card_W : Nat.card ↥(O ⊓ θ.ker) = 8 ∧ ∀ x ∈ O, θ x = 1 → p x ∈ zPerp := by
  set W : Subgroup Γ := O ⊓ θ.ker with hW
  have hmemW : ∀ x, x ∈ W ↔ x ∈ O ∧ θ x = 1 := fun x => by
    rw [hW, Subgroup.mem_inf, MonoidHom.mem_ker]
  have hsub : zPerp ⊆ p '' (W : Set Γ) := by
    intro w hw
    obtain ⟨x, hxO, hx1, hpx⟩ := H.exists_of_mem_zPerp hw
    exact ⟨x, (hmemW x).2 ⟨hxO, hx1⟩, hpx⟩
  have hinj : Set.InjOn p (W : Set Γ) := fun a ha b hb hab =>
    H.pi.inj a b ((hmemW a).1 ha).2 ((hmemW b).1 hb).2 hab
  have hcard : (p '' (W : Set Γ)).ncard = Nat.card W :=
    hinj.ncard_image.trans (Nat.card_coe_set_eq (W : Set Γ)).symm
  have h8 : 8 ≤ Nat.card W := by
    have := Set.ncard_le_ncard hsub
    rwa [ncard_zPerp, hcard] at this
  have hdvd : Nat.card W ∣ 16 := by
    rw [← H.card_ker]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hne : Nat.card W ≠ 16 := by
    intro h16
    apply H.not_le
    have heq : W = θ.ker :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h16, H.card_ker])
    rw [← heq]
    exact inf_le_left
  have h8' : Nat.card W = 8 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      omega
    have hk2 : 2 ≤ k := by omega
    have := Nat.mul_le_mul_left (Nat.card W) hk2
    omega
  refine ⟨h8', fun x hxO hx1 => ?_⟩
  have heq : zPerp = p '' (W : Set Γ) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hcard, h8', ncard_zPerp]))
  rw [heq]
  exact ⟨x, (hmemW x).2 ⟨hxO, hx1⟩, rfl⟩

theorem z_mem : z ∈ O := by
  obtain ⟨x, hxO, hx1, hpx⟩ := H.exists_of_mem_zPerp zBar_mem_zPerp
  have : x = z := H.pi.inj x z hx1 H.theta_z (hpx.trans H.p_z.symm)
  rwa [this] at hxO

end OData

theorem card_eq_inf_mul (θ : Γ →* Perm (Fin 6)) (O : Subgroup Γ) :
    Nat.card O = Nat.card ↥(O ⊓ θ.ker) * Nat.card ↥(O.map θ) := by
  have h1 := Subgroup.card_ker_mul_card_range (θ.comp O.subtype)
  have hrange : (θ.comp O.subtype).range = O.map θ := by
    ext σ
    simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k.2, hk⟩, fun ⟨m, hm, hk⟩ => ⟨⟨m, hm⟩, hk⟩⟩
  have hker : Nat.card (θ.comp O.subtype).ker = Nat.card ↥(O ⊓ θ.ker) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun k => ⟨((k : ↥O) : Γ), Subgroup.mem_inf.2 ⟨k.1.2, k.2⟩⟩) ⟨?_, ?_⟩)
    · intro k k' h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h1)
    · intro u
      have hu := Subgroup.mem_inf.1 u.2
      exact ⟨⟨⟨u.1, hu.1⟩, hu.2⟩, rfl⟩
  rw [hker, hrange] at h1
  exact h1.symm

namespace OData

variable {θ : Γ →* Perm (Fin 6)} {p : Γ → permBar 6} {z : Γ} {O : Subgroup Γ}
  (H : OData θ p z O)
include H

theorem card_O : Nat.card ↥O = 32 := by
  rw [card_eq_inf_mul θ O, H.card_W.1, H.map_O, card_V0]

theorem center_le {x : Γ} (hx : x ∈ O) (hc : ∀ y ∈ O, x * y = y * x) : x = 1 ∨ x = z := by
  by_cases h1 : θ x = 1
  · have hpx := H.card_W.2 x hx h1
    obtain ⟨o₁, ho₁, hθ₁⟩ := H.exists_lift b1_mem_V0
    obtain ⟨o₂, ho₂, hθ₂⟩ := H.exists_lift b2_mem_V0
    have hfix : ∀ o ∈ O, barAct (θ o) (p x) = p x := by
      intro o ho
      have h := H.pi.conj o x h1
      rw [show o * x * o⁻¹ = x from mul_inv_eq_iff_eq_mul.2 (hc o ho).symm] at h
      exact h.symm
    have h1' := hfix o₁ ho₁
    rw [hθ₁] at h1'
    have h2' := hfix o₂ ho₂
    rw [hθ₂] at h2'
    rcases eq_of_fix_b1_b2 hpx h1' h2' with h0 | h0
    · exact Or.inl (H.pi.inj x 1 h1 (map_one θ) (h0.trans H.p_one.symm))
    · exact Or.inr (H.pi.inj x z h1 H.theta_z (h0.trans H.p_z.symm))
  · exfalso
    obtain ⟨w, hw, hne⟩ := exists_not_fix_zPerp (H.mem_V0 hx) h1
    obtain ⟨y, hyO, hy1, rfl⟩ := H.exists_of_mem_zPerp hw
    apply hne
    have h := H.pi.conj x y hy1
    rw [show x * y * x⁻¹ = y from mul_inv_eq_iff_eq_mul.2 (hc y hyO)] at h
    exact h.symm

theorem kap_mem_of_right {x y : Γ} (hx : x ∈ O) (hy : y ∈ O) (hy1 : θ y = 1) :
    p (x * y * x⁻¹ * y⁻¹) ∈ Zs := by
  rw [H.p_conj_comm hy1]
  exact mem_Zs.2 (barAct_sub_mem_zPerp (H.mem_V0 hx) (H.card_W.2 y hy hy1))

theorem p_comm_symm {x y : Γ} (hx : x ∈ O) (hy : y ∈ O) :
    p (y * x * y⁻¹ * x⁻¹) = p (x * y * x⁻¹ * y⁻¹) := by
  have e : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
  rw [e, H.p_inv (H.theta_comm hx hy)]

theorem kap_mem_of_left {x y : Γ} (hx : x ∈ O) (hx1 : θ x = 1) (hy : y ∈ O) :
    p (x * y * x⁻¹ * y⁻¹) ∈ Zs := by
  rw [← H.p_comm_symm hx hy]
  exact H.kap_mem_of_right hy hx hx1

theorem kap_mul_left {x x' y : Γ} (hx : x ∈ O) (hx' : x' ∈ O) (hy : y ∈ O) :
    p (x * x' * y * (x * x')⁻¹ * y⁻¹) -
      (p (x * y * x⁻¹ * y⁻¹) + p (x' * y * x'⁻¹ * y⁻¹)) ∈ Zs := by
  have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
      (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
  have hA : θ (x' * y * x'⁻¹ * y⁻¹) = 1 := H.theta_comm hx' hy
  have hB : θ (x * y * x⁻¹ * y⁻¹) = 1 := H.theta_comm hx hy
  have hC : θ (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hA]
    group
  rw [e, H.pi.mul _ _ hC hB, H.pi.conj x _ hA]
  have hw := barAct_sub_mem_zPerp (H.mem_V0 hx) (H.card_W.2 _ (H.comm_mem hx' hy) hA)
  have e2 : barAct (θ x) (p (x' * y * x'⁻¹ * y⁻¹)) + p (x * y * x⁻¹ * y⁻¹) -
      (p (x * y * x⁻¹ * y⁻¹) + p (x' * y * x'⁻¹ * y⁻¹)) =
      barAct (θ x) (p (x' * y * x'⁻¹ * y⁻¹)) - p (x' * y * x'⁻¹ * y⁻¹) := by
    letI := permBarACG 6
    abel
  rw [e2]
  exact mem_Zs.2 hw

theorem kap_mul_right {x y y' : Γ} (hx : x ∈ O) (hy : y ∈ O) (hy' : y' ∈ O) :
    p (x * (y * y') * x⁻¹ * (y * y')⁻¹) -
      (p (x * y * x⁻¹ * y⁻¹) + p (x * y' * x⁻¹ * y'⁻¹)) ∈ Zs := by
  have e : x * (y * y') * x⁻¹ * (y * y')⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group
  have hA : θ (x * y' * x⁻¹ * y'⁻¹) = 1 := H.theta_comm hx hy'
  have hB : θ (x * y * x⁻¹ * y⁻¹) = 1 := H.theta_comm hx hy
  have hC : θ (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hA]
    group
  rw [e, H.pi.mul _ _ hB hC, H.pi.conj y _ hA]
  have hw := barAct_sub_mem_zPerp (H.mem_V0 hy) (H.card_W.2 _ (H.comm_mem hx hy') hA)
  have e2 : p (x * y * x⁻¹ * y⁻¹) + barAct (θ y) (p (x * y' * x⁻¹ * y'⁻¹)) -
      (p (x * y * x⁻¹ * y⁻¹) + p (x * y' * x⁻¹ * y'⁻¹)) =
      barAct (θ y) (p (x * y' * x⁻¹ * y'⁻¹)) - p (x * y' * x⁻¹ * y'⁻¹) := by
    letI := permBarACG 6
    abel
  rw [e2]
  exact mem_Zs.2 hw

theorem kap_congr_left {x x' y : Γ} (hx : x ∈ O) (hx' : x' ∈ O) (hy : y ∈ O)
    (hθ : θ x = θ x') :
    p (x' * y * x'⁻¹ * y⁻¹) - p (x * y * x⁻¹ * y⁻¹) ∈ Zs := by
  have hw : x⁻¹ * x' ∈ O := O.mul_mem (O.inv_mem hx) hx'
  have hw1 : θ (x⁻¹ * x') = 1 := by rw [map_mul, map_inv, hθ, inv_mul_cancel]
  have h1 := H.kap_mul_left hx hw hy
  have h2 := H.kap_mem_of_left hw hw1 hy
  rw [mul_inv_cancel_left] at h1
  have h3 := Zs.add_mem h1 h2
  convert h3 using 1
  letI := permBarACG 6
  abel

theorem kap_congr_right {x y y' : Γ} (hx : x ∈ O) (hy : y ∈ O) (hy' : y' ∈ O)
    (hθ : θ y = θ y') :
    p (x * y' * x⁻¹ * y'⁻¹) - p (x * y * x⁻¹ * y⁻¹) ∈ Zs := by
  have hw : y⁻¹ * y' ∈ O := O.mul_mem (O.inv_mem hy) hy'
  have hw1 : θ (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, hθ, inv_mul_cancel]
  have h1 := H.kap_mul_right hx hy hw
  have h2 := H.kap_mem_of_right hx hw hw1
  rw [mul_inv_cancel_left] at h1
  have h3 := Zs.add_mem h1 h2
  convert h3 using 1
  letI := permBarACG 6
  abel

theorem kap_congr {x x' y y' : Γ} (hx : x ∈ O) (hx' : x' ∈ O) (hy : y ∈ O) (hy' : y' ∈ O)
    (hθx : θ x = θ x') (hθy : θ y = θ y') :
    p (x' * y' * x'⁻¹ * y'⁻¹) - p (x * y * x⁻¹ * y⁻¹) ∈ Zs := by
  have h1 := H.kap_congr_left hx hx' hy' hθx
  have h2 := H.kap_congr_right hx hy hy' hθy
  have h3 := Zs.add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3

theorem decomp {A : Γ → Prop} {o₁ o₂ : Γ} (ho₁ : o₁ ∈ O) (ho₂ : o₂ ∈ O)
    (hθ₁ : θ o₁ = b1) (hθ₂ : θ o₂ = b2) (hmul : ∀ a b, A a → A b → A (a * b))
    (hW : ∀ x ∈ O, θ x = 1 → A x) (h₁ : A o₁) (h₂ : A o₂) : ∀ x ∈ O, A x := by
  intro x hx
  have key : ∀ c, A c → c ∈ O → θ c = θ x → A x := by
    intro c hcA hcO hθc
    have hmem : c⁻¹ * x ∈ O := O.mul_mem (O.inv_mem hcO) hx
    have h1 : θ (c⁻¹ * x) = 1 := by rw [map_mul, map_inv, hθc, inv_mul_cancel]
    have h2 := hmul c _ hcA (hW _ hmem h1)
    rwa [mul_inv_cancel_left] at h2
  rcases mem_klein4_45_iff.1 (H.mem_V0 hx) with h | h | h | h
  · exact hW x hx h
  · exact key o₁ h₁ ho₁ (hθ₁.trans h.symm)
  · exact key o₂ h₂ ho₂ (hθ₂.trans h.symm)
  · exact key (o₁ * o₂) (hmul _ _ h₁ h₂) (O.mul_mem ho₁ ho₂) (by rw [map_mul, hθ₁, hθ₂, h])

theorem kap_b1_b2 {o₁ o₂ : Γ} (ho₁ : o₁ ∈ O) (ho₂ : o₂ ∈ O) (hθ₁ : θ o₁ = b1)
    (hθ₂ : θ o₂ = b2) : p (o₁ * o₂ * o₁⁻¹ * o₂⁻¹) ∈ Zs := by
  obtain ⟨y, hyz, hyθ⟩ := H.exists_c3
  obtain ⟨o₁', ho₁'⟩ : ∃ o₁', o₁' = y * o₁ * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨o₂', ho₂'⟩ : ∃ o₂', o₂' = y * o₂ * y⁻¹ := ⟨_, rfl⟩
  have ho₁'O : o₁' ∈ O := by
    rw [ho₁']
    exact H.norm_cent y hyz o₁ ho₁
  have ho₂'O : o₂' ∈ O := by
    rw [ho₂']
    exact H.norm_cent y hyz o₂ ho₂
  have hθ₁' : θ o₁' = b2 := by
    rw [ho₁', map_mul, map_mul, map_inv, hθ₁, hyθ]
    exact c3_conj_b1
  have hθ₂' : θ o₂' = b1 * b2 := by
    rw [ho₂', map_mul, map_mul, map_inv, hθ₂, hyθ]
    exact c3_conj_b2
  have hθc : θ (o₁ * o₂ * o₁⁻¹ * o₂⁻¹) = 1 := H.theta_comm ho₁ ho₂
  have hp : p (o₁' * o₂' * o₁'⁻¹ * o₂'⁻¹) = barAct c3 (p (o₁ * o₂ * o₁⁻¹ * o₂⁻¹)) := by
    have hc : o₁' * o₂' * o₁'⁻¹ * o₂'⁻¹ = y * (o₁ * o₂ * o₁⁻¹ * o₂⁻¹) * y⁻¹ := by
      rw [ho₁', ho₂']
      group
    rw [hc, H.pi.conj y _ hθc, hyθ]
  have h1 := H.kap_congr ho₂ ho₁'O (O.mul_mem ho₁ ho₂) ho₂'O (hθ₂.trans hθ₁'.symm)
    (by rw [map_mul, hθ₁, hθ₂, hθ₂'])
  have h2 := H.kap_mul_right ho₂ ho₁ ho₂
  have h3 : p (o₂ * o₂ * o₂⁻¹ * o₂⁻¹) = 0 := by
    have e : o₂ * o₂ * o₂⁻¹ * o₂⁻¹ = 1 := by group
    rw [e, H.p_one]
  have h4 := H.p_comm_symm ho₁ ho₂
  rw [h3, h4] at h2
  rw [hp] at h1
  have hw : p (o₁ * o₂ * o₁⁻¹ * o₂⁻¹) ∈ zPerp := H.card_W.2 _ (H.comm_mem ho₁ ho₂) hθc
  have h5 := Zs.add_mem h1 h2
  have h6 : barAct c3 (p (o₁ * o₂ * o₁⁻¹ * o₂⁻¹)) - p (o₁ * o₂ * o₁⁻¹ * o₂⁻¹) ∈ Zs := by
    convert h5 using 1
    letI := permBarACG 6
    abel
  exact mem_Zs.2 (eq_of_c3_sub hw (mem_Zs.1 h6))

theorem comm_mem_Zs {x y : Γ} (hx : x ∈ O) (hy : y ∈ O) : p (x * y * x⁻¹ * y⁻¹) ∈ Zs := by
  obtain ⟨o₁, ho₁, hθ₁⟩ := H.exists_lift b1_mem_V0
  obtain ⟨o₂, ho₂, hθ₂⟩ := H.exists_lift b2_mem_V0
  have hd := H.kap_b1_b2 ho₁ ho₂ hθ₁ hθ₂
  have hone : ∀ a, p (a * a * a⁻¹ * a⁻¹) ∈ Zs := fun a => by
    have e : a * a * a⁻¹ * a⁻¹ = 1 := by group
    rw [e, H.p_one]
    exact Zs.zero_mem
  have hrow : ∀ a ∈ O, p (a * o₁ * a⁻¹ * o₁⁻¹) ∈ Zs → p (a * o₂ * a⁻¹ * o₂⁻¹) ∈ Zs →
      ∀ y ∈ O, p (a * y * a⁻¹ * y⁻¹) ∈ Zs := by
    intro a ha h₁ h₂
    have key := H.decomp (A := fun y => y ∈ O ∧ p (a * y * a⁻¹ * y⁻¹) ∈ Zs) ho₁ ho₂ hθ₁ hθ₂
      (fun u v hu hv => ⟨O.mul_mem hu.1 hv.1, by
        have h := H.kap_mul_right ha hu.1 hv.1
        have h' := Zs.add_mem h (Zs.add_mem hu.2 hv.2)
        rwa [sub_add_cancel] at h'⟩)
      (fun y hy hy1 => ⟨hy, H.kap_mem_of_right ha hy hy1⟩) ⟨ho₁, h₁⟩ ⟨ho₂, h₂⟩
    exact fun y hy => (key y hy).2
  have hr₁ := hrow o₁ ho₁ (hone o₁) hd
  have hr₂ := hrow o₂ ho₂ (by rw [H.p_comm_symm ho₁ ho₂]; exact hd) (hone o₂)
  have key := H.decomp (A := fun a => a ∈ O ∧ ∀ y ∈ O, p (a * y * a⁻¹ * y⁻¹) ∈ Zs) ho₁ ho₂ hθ₁ hθ₂
    (fun u v hu hv => ⟨O.mul_mem hu.1 hv.1, fun y hy => by
      have h := H.kap_mul_left hu.1 hv.1 hy
      have h' := Zs.add_mem h (Zs.add_mem (hu.2 y hy) (hv.2 y hy))
      rwa [sub_add_cancel] at h'⟩)
    (fun a ha ha1 => ⟨ha, fun y hy => H.kap_mem_of_left ha ha1 hy⟩) ⟨ho₁, hr₁⟩ ⟨ho₂, hr₂⟩
  exact (key x hx).2 y hy

theorem comm_eq {x y : Γ} (hx : x ∈ O) (hy : y ∈ O) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z := by
  have hθ := H.theta_comm hx hy
  rcases mem_Zs.1 (H.comm_mem_Zs hx hy) with h0 | h0
  · exact Or.inl (H.pi.inj _ 1 hθ (map_one θ) (h0.trans H.p_one.symm))
  · exact Or.inr (H.pi.inj _ z hθ H.theta_z (h0.trans H.p_z.symm))

theorem lemma5 : z ∈ O ∧ Nat.card ↥O = 32 ∧
    (∀ x ∈ O, (∀ y ∈ O, x * y = y * x) → x = 1 ∨ x = z) ∧
    ∀ x ∈ O, ∀ y ∈ O, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z :=
  ⟨H.z_mem, H.card_O, fun _ hx hc => H.center_le hx hc, fun _ hx _ hy => H.comm_eq hx hy⟩

end OData

end Core

end Lemma5

end Q16Alt

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 6)

theorem theta_eq_one_iff_mem_pCore (hR : Nat.card ↥(Rc X) ≤ 2) (m : ↥M) :
    C.θ m = 1 ↔ (m : G) ∈ CFSG.Open.pCoreOf 2 M := by
  rw [← MonoidHom.mem_ker, C.theta_ker_eq hR, Subgroup.mem_subgroupOf]

end Cfg

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

noncomputable def piM (m : ↥M) : permBar 6 := by
  classical
  exact if h : (m : G) ∈ CFSG.Open.pCoreOf 2 M then Multiplicative.toAdd (D.piQ ⟨m, h⟩) else 0

theorem piM_of_mem {m : ↥M} (h : (m : G) ∈ CFSG.Open.pCoreOf 2 M) :
    D.piM m = Multiplicative.toAdd (D.piQ ⟨m, h⟩) := by
  unfold piM
  rw [dif_pos h]

theorem piLike (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) :
    Q16Alt.Lemma5.PiLike C.θ D.piM where
  mul a b ha hb := by
    have ha' := (C.theta_eq_one_iff_mem_pCore hR a).1 ha
    have hb' := (C.theta_eq_one_iff_mem_pCore hR b).1 hb
    have hab : ((a * b : ↥M) : G) ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem ha' hb'
    rw [D.piM_of_mem hab, D.piM_of_mem ha', D.piM_of_mem hb']
    have e : (⟨((a * b : ↥M) : G), hab⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
        ⟨(a : G), ha'⟩ * ⟨(b : G), hb'⟩ := rfl
    rw [e, map_mul, toAdd_mul]
  conj m q hq := by
    have hq' := (C.theta_eq_one_iff_mem_pCore hR q).1 hq
    have hmq : ((m * q * m⁻¹ : ↥M) : G) ∈ CFSG.Open.pCoreOf 2 M :=
      pCoreOf_normalized M m.2 hq'
    rw [D.piM_of_mem hmq, D.piM_of_mem hq']
    exact D.piQ_conj m ⟨(q : G), hq'⟩ ⟨_, hmq⟩ rfl
  inj a b ha hb h := by
    have ha' := (C.theta_eq_one_iff_mem_pCore hR a).1 ha
    have hb' := (C.theta_eq_one_iff_mem_pCore hR b).1 hb
    rw [D.piM_of_mem ha', D.piM_of_mem hb'] at h
    have h1 := D.q16_piQ_injective hR hQ (Multiplicative.toAdd.injective h)
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  surj u := by
    obtain ⟨q, -, hq⟩ := D.heart_mem_piQ_Q u
    have hqM : (q : G) ∈ M := pCoreOf_le_self M q.2
    refine ⟨⟨(q : G), hqM⟩, (C.theta_eq_one_iff_mem_pCore hR _).2 q.2, ?_⟩
    rw [D.piM_of_mem q.2]
    exact congrArg Multiplicative.toAdd hq

include D in
theorem q16_lemma5 (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 M)
    (hπz : Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = Q16Alt.zBar)
    {O : Subgroup G} (hOM : O ≤ M)
    (hθO : (O.subgroupOf M).map C.θ = klein4 ({4, 5} : Finset (Fin 6))ᶜ)
    (hQO : ¬ CFSG.Open.pCoreOf 2 M ≤ O)
    (hOQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ o ∈ O, q * o * q⁻¹ ∈ O)
    (hOy : ∀ y ∈ CMOf M z, ∀ o ∈ O, y * o * y⁻¹ ∈ O) :
    z ∈ O ∧ Nat.card O = 32 ∧ (∀ x ∈ O, (∀ y ∈ O, x * y = y * x) → x = 1 ∨ x = z) ∧
      ∀ x ∈ O, ∀ y ∈ O, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z := by
  have hQM : CFSG.Open.pCoreOf 2 M ≤ M := pCoreOf_le_self M
  have hzM : z ∈ M := hQM hz
  have hdata : Q16Alt.Lemma5.OData C.θ D.piM (⟨z, hzM⟩ : ↥M) (O.subgroupOf M) :=
    { pi := D.piLike hR hQ
      card_ker := by
        rw [C.theta_ker_eq hR]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv).trans hQ
      theta_z := (C.theta_eq_one_iff_mem_pCore hR ⟨z, hzM⟩).2 hz
      p_z := by
        rw [D.piM_of_mem (m := ⟨z, hzM⟩) hz]
        exact hπz
      map_O := hθO
      not_le := fun h => hQO (fun q hq => by
        have hmem : (⟨q, hQM hq⟩ : ↥M) ∈ C.θ.ker :=
          (C.theta_eq_one_iff_mem_pCore hR ⟨q, hQM hq⟩).2 hq
        exact h hmem)
      norm_ker := fun q hq o ho => by
        exact hOQ (q : G) ((C.theta_eq_one_iff_mem_pCore hR q).1 hq) (o : G) ho
      norm_cent := fun y hy o ho => by
        have hyG : (y : G) * z = z * y := congrArg Subtype.val hy
        have hmem : (y : G) ∈ CMOf M z := Subgroup.mem_inf.2 ⟨y.2,
          mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 hyG)⟩
        exact hOy (y : G) hmem (o : G) ho
      exists_c3 := by
        have hmem := D.altOn_le_theta_CMOf_six hz (I := {4, 5}) (by decide) hπz (Or.inr rfl)
          Q16Alt.c3_mem_altOn
        obtain ⟨y, hy, hyθ⟩ := Subgroup.mem_map.1 hmem
        refine ⟨y, ?_, hyθ⟩
        have hy' : (y : G) ∈ CMOf M z := Subgroup.mem_subgroupOf.1 hy
        have h := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hy').2
        exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 h) }
  obtain ⟨h1, h2, h3, h4⟩ := hdata.lemma5
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [← h2]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOM).toEquiv).symm
  · intro x hx hc
    rcases h3 ⟨x, hOM hx⟩ hx (fun y hy => Subtype.ext (hc (y : G) hy)) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · intro x hx y hy
    rcases h4 ⟨x, hOM hx⟩ hx ⟨y, hOM hy⟩ hy with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
