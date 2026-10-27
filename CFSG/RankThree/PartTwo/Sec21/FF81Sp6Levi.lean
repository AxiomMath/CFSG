module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Transv
public import CFSG.RankThree.PartTwo.Sec21.FF81Sp6LeviJ
public import CFSG.RankThree.PartTwo.Sec21.FF81Sp6LeviNorm
public import CFSG.RankThree.PartTwo.Sec21.FF81Sp6LeviRed
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv (card_map_inf_cen)

namespace Sp6Levi

abbrev LeviJ {G : Type} [Group G] (L : Subgroup G) (b₁ b₂ b₃ : G) : Prop :=
  ∃ J : Subgroup G, J ≤ L ⊓ Cen b₂ ∧ Nonempty (↥J ≃* Equiv.Perm (Fin 6)) ∧ b₁ ∈ J ∧ b₃ ∈ J ∧
    ∀ y ∈ L ⊓ Cen b₂, ∃ k : ℕ, ∃ j ∈ J, y = b₂ ^ k * j

theorem LeviJ.map {G G' : Type} [Group G] [Group G'] {f : G →* G'} (hf : Function.Injective f)
    {L : Subgroup G} {b₁ b₂ b₃ : G} (h : LeviJ L b₁ b₂ b₃) :
    LeviJ (L.map f) (f b₁) (f b₂) (f b₃) := by
  obtain ⟨J, hJ, ⟨e⟩, h1, h3, hprod⟩ := h
  refine ⟨J.map f, ?_, ⟨(Subgroup.equivMapOfInjective J f hf).symm.trans e⟩,
    Subgroup.mem_map_of_mem f h1, Subgroup.mem_map_of_mem f h3, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨hjL, hjC⟩ := Subgroup.mem_inf.mp (hJ hj)
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem f hjL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hjC ⊢
    rw [← map_mul, ← map_mul, hjC]
  · intro y' hy'
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.mp hy'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hyL
    have hyC' : y ∈ Cen b₂ := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      apply hf
      simpa only [map_mul] using hyC
    obtain ⟨k, j, hj, rfl⟩ := hprod y (Subgroup.mem_inf.mpr ⟨hy, hyC'⟩)
    exact ⟨k, f j, Subgroup.mem_map_of_mem f hj, by simp only [map_mul, map_pow]⟩

private theorem cen_sq {z : H6} (hz : z ^ 3 = 1) : Cen (z ^ 2) = Cen z := by
  have h4 : (z ^ 2) ^ 2 = z := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hz, one_mul]
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h := (show Commute g (z ^ 2) from hg).pow_right 2
    rw [h4] at h
    exact h
  · intro hg
    exact (show Commute g z from hg).pow_right 2

private theorem cen_pow_val {z : H6} (hz : z ^ 3 = 1) {a : ZMod 3} (ha : a ≠ 0) :
    Cen (z ^ a.val) = Cen z := by
  rcases val_eq_one_or_two ha with h | h <;> rw [h]
  · rw [pow_one]
  · exact cen_sq hz

private theorem pow_val_pow_mul {z : H6} (hz : z ^ 3 = 1) {a : ZMod 3} (ha : a ≠ 0) (k : ℕ) :
    (z ^ a.val) ^ (k * a.val) = z ^ k := by
  rcases val_eq_one_or_two ha with h | h <;> rw [h]
  · simp
  · rw [← pow_mul, show 2 * (k * 2) = k + 3 * k by ring, pow_add, pow_mul, hz, one_pow, mul_one]

section H6


theorem levi_H6 {p₁ p₂ p₃ : Fin 3} {a₁ a₂ a₃ : ZMod 3} (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃)
    (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0) (ha₁ : a₁ ≠ 0) :
    LeviJ ⊤ (zH p₁ ^ a₁.val) (zH p₂ ^ a₂.val) (zH p₃ ^ a₃.val) ∧
      LeviN ⊤ (zH p₂ ^ a₂.val) (zH p₃ ^ a₃.val) := by
  refine ⟨?_, leviN_zH h23 ha₂ ha₃⟩
  have hcen : Cen (zH p₂ ^ a₂.val) = Cen (zH p₂) := cen_pow_val (zH_pow_three _) ha₂
  refine ⟨levJ p₂, ?_, nonempty_levJ_equiv p₂, pow_mem (zH_mem_levJ h12) _,
    pow_mem (zH_mem_levJ h23.symm) _, ?_⟩
  · intro j hj
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩
    rw [hcen, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_zH_of_mem_levJ p₂ hj).eq.symm
  · intro y hy
    obtain ⟨-, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [hcen] at hyC
    obtain ⟨k, j, hj, rfl⟩ := exists_mul_of_mem_cen p₂ hyC
    exact ⟨k * a₂.val, j, hj, by rw [pow_val_pow_mul (zH_pow_three _) ha₂]⟩

end H6

end Sp6Levi

theorem kf_sp6Levi : KF_Sp6Levi := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB hBc hmono
  classical
  have hc₂ : Nat.card ↥(L ⊓ Cen b₂) = 2160 :=
    (kf_sp6Transv X L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB hBc hmono).1
  have e12 : ({b₂, b₁, b₃} : Set X) = {b₁, b₂, b₃} := Set.insert_comm _ _ _
  have e13 : ({b₁, b₃, b₂} : Set X) = {b₁, b₂, b₃} := by rw [Set.pair_comm]
  have hc₁ : Nat.card ↥(L ⊓ Cen b₁) = 2160 := by
    refine (kf_sp6Transv X L hL b₂ b₁ b₃ hb₂ hb₁ hb₃ (by rw [e12]; exact hB)
      (by rw [e12]; exact hBc) ?_).1
    intro n hn hnN x hx
    rw [e12] at hnN hx
    have h := hmono n hn hnN x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  have hc₃ : Nat.card ↥(L ⊓ Cen b₃) = 2160 := by
    refine (kf_sp6Transv X L hL b₁ b₃ b₂ hb₁ hb₃ hb₂ (by rw [e13]; exact hB)
      (by rw [e13]; exact hBc) ?_).1
    intro n hn hnN x hx
    rw [e13] at hnN hx
    have h := hmono n hn hnN x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  obtain ⟨θ⟩ := nonempty_mulEquiv_H6_of_stated hL
  set f : H6 →* X := L.subtype.comp θ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.symm.injective
  have hfa : ∀ y : X, ∀ hy : y ∈ L, f (θ ⟨y, hy⟩) = y := fun y hy => by simp [hfdef]
  have hfL : (⊤ : Subgroup H6).map f = L := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (θ.symm x).2
    · intro hy
      exact ⟨θ ⟨y, hy⟩, Subgroup.mem_top _, hfa y hy⟩
  set c₁ := θ ⟨b₁, hb₁⟩
  set c₂ := θ ⟨b₂, hb₂⟩
  set c₃ := θ ⟨b₃, hb₃⟩
  have e₁ : f c₁ = b₁ := hfa _ _
  have e₂ : f c₂ = b₂ := hfa _ _
  have e₃ : f c₃ = b₃ := hfa _ _
  have hcl : (Subgroup.closure ({c₁, c₂, c₃} : Set H6)).map f =
      Subgroup.closure ({b₁, b₂, b₃} : Set X) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, e₁, e₂, e₃]
  have hBc' : Nat.card (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) = 27 := by
    rw [← Subgroup.card_map_of_injective hf, hcl, hB.2]
    norm_num
  have hBe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) := by
    have hB0 : CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({b₁, b₂, b₃} : Set X)) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hB.1
    obtain ⟨hcomm, hpow⟩ := hB0
    have hmemf : ∀ x ∈ Subgroup.closure ({c₁, c₂, c₃} : Set H6),
        f x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set X) := fun x hx => by
      rw [← hcl]; exact Subgroup.mem_map_of_mem f hx
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · have := congrArg Subtype.val (hcomm.is_comm.comm ⟨f a, hmemf a a.2⟩ ⟨f b, hmemf b b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · rw [map_pow, hpow _ (hmemf x hx), map_one]
  have hcen : ∀ (c : H6) (b : X), f c = b → Nat.card ↥(L ⊓ Cen b) = 2160 →
      Nat.card (Subgroup.centralizer {c}) = 2160 := by
    intro c b hcb hb
    have h := card_map_inf_cen hf (⊤ : Subgroup H6) c
    rw [hfL, hcb, hb, top_inf_eq] at h
    exact h.symm
  obtain ⟨g, p₁, p₂, p₃, a₁, a₂, a₃, h12, h23, ha₁, ha₂, ha₃, ec₁, ec₂, ec₃⟩ :=
    exists_conj_torus hBe hBc' (hcen c₁ b₁ e₁ hc₁) (hcen c₂ b₂ e₂ hc₂) (hcen c₃ b₃ e₃ hc₃)
  obtain ⟨hJ, hN⟩ := Sp6Levi.levi_H6 h12 h23 ha₂ ha₃ ha₁
  set F : H6 →* X := f.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := hf.comp (MulAut.conj g).injective
  have hFL : (⊤ : Subgroup H6).map F = L := by
    rw [hFdef, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective,
      hfL]
  have hF₁ : F (zH p₁ ^ a₁.val) = b₁ := by
    rw [hFdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ec₁, e₁]
  have hF₂ : F (zH p₂ ^ a₂.val) = b₂ := by
    rw [hFdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ec₂, e₂]
  have hF₃ : F (zH p₃ ^ a₃.val) = b₃ := by
    rw [hFdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ec₃, e₃]
  have h1 := hJ.map hF
  have h2 := hN.map hF
  rw [hFL, hF₁, hF₂, hF₃] at h1
  rw [hFL, hF₂, hF₃] at h2
  exact ⟨h1, h2⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
