module

public import CFSG.OddTranspositions.PartThree.Twelve.FourSp
public import CFSG.OddTranspositions.PartThree.Twelve.TenModel
public import CFSG.OddTranspositions.PartThree.Twelve.SixComponent
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.SevenFourEight.SevenSix
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Timmesfeld.Connectivity
open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull

section Multiplier

variable {K : Type} [Group K] [Finite K]

theorem inf_commutator_eq_bot_of_multiplier {M : Subgroup K} [M.Normal]
    (hMZ : M ≤ Subgroup.center K) {x : K} (hx : x * x = 1)
    (hcos : ∀ h : K, h ∈ commutator K ∨ x * h ∈ commutator K)
    (hperf : ⁅commutator (K ⧸ M), commutator (K ⧸ M)⁆ = commutator (K ⧸ M))
    (hmult : ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* ↥(commutator (K ⧸ M))),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → φ.ker = ⊥) :
    M ⊓ commutator K = ⊥ := by
  have hK' : (commutator K).map (QuotientGroup.mk' M) = commutator (K ⧸ M) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M),
      commutator_def]
  have hmem : ∀ k : ↥(commutator K),
      (QuotientGroup.mk' M).comp (commutator K).subtype k ∈ commutator (K ⧸ M) :=
    fun k => hK' ▸ ⟨k, k.2, rfl⟩
  let φ : ↥(commutator K) →* ↥(commutator (K ⧸ M)) :=
    ((QuotientGroup.mk' M).comp (commutator K).subtype).codRestrict _ hmem
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hK'] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker : ∀ k, k ∈ φ.ker ↔ (k : K) ∈ M := by
    intro k
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcen : φ.ker ≤ Subgroup.center ↥(commutator K) := fun k hk =>
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hMZ ((hker k).mp hk)) g)
  have hcomm : φ.ker ≤ commutator ↥(commutator K) := by
    intro k _
    have h1 : (k : K) ∈ ⁅commutator K, commutator K⁆ :=
      commutator_le_commutator_commutator hMZ hx hcos hperf k.2
    rw [← Subgroup.map_subtype_commutator] at h1
    obtain ⟨k', hk', he⟩ := h1
    rwa [show k' = k from Subtype.ext he] at hk'
  have hbot := hmult _ φ hsurj hcen hcomm
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, hz.2⟩ : ↥(commutator K)) ∈ φ.ker := (hker _).mpr hz.1
  rw [hbot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

end Multiplier

section Generic

variable {G : Type} [Group G]

private theorem ker_eq_bot_of_commutator_eq_top (htop : commutator G = ⊤)
    (hmult : ∀ (Γ : Type) [Group Γ] (φ : Γ →* G), Function.Surjective φ →
      φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → φ.ker = ⊥)
    (Γ : Type) [Group Γ] (φ : Γ →* ↥(commutator G)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcomm : φ.ker ≤ commutator Γ) : φ.ker = ⊥ := by
  let θ : ↥(commutator G) ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hker : (θ.toMonoidHom.comp φ).ker = φ.ker := by
    ext g
    simp [MonoidHom.mem_ker]
  have h1 := hmult Γ (θ.toMonoidHom.comp φ) (θ.surjective.comp hφ)
    (by rw [hker]; exact hcen) (by rw [hker]; exact hcomm)
  rwa [hker] at h1

private theorem center_eq_zpowers_of_inf_eq_bot {u x₀ : G}
    (hbot : Subgroup.center G ⊓ commutator G = ⊥) (hu : u ∈ Subgroup.center G)
    (hcos : ∀ h : G, h ∈ commutator G ∨ x₀ * h ∈ commutator G)
    (hxu : x₀ * u ∈ commutator G) : Subgroup.center G = Subgroup.zpowers u := by
  refine le_antisymm (fun z hz => ?_) ((Subgroup.zpowers_le).mpr hu)
  rcases hcos z with hz' | hz'
  · have h2 : z ∈ Subgroup.center G ⊓ commutator G := ⟨hz, hz'⟩
    rw [hbot, Subgroup.mem_bot] at h2
    rw [h2]
    exact Subgroup.one_mem _
  · have h3 : (x₀ * u)⁻¹ * (x₀ * z) ∈ commutator G :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hxu) hz'
    rw [show (x₀ * u)⁻¹ * (x₀ * z) = u⁻¹ * z by group] at h3
    have h4 : u⁻¹ * z ∈ Subgroup.center G ⊓ commutator G :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hz, h3⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h4
    rw [← h4]
    exact Subgroup.mem_zpowers u

private theorem mem_or_mul_mem_of_mem_normalizer_of_image {H : Subgroup G} {S : Type} [Group S]
    {ρ : H →* S} {L : Subgroup G} {O : Subgroup S} (hO : Subgroup.normalizer (O : Set S) = O)
    (himg : ∀ y, y ∈ O ↔ ∃ x : H, (x : G) ∈ L ∧ ρ x = y) {u : H}
    (hker : ∀ z, ρ z = 1 → z = 1 ∨ z = u) (hLu : ∀ x ∈ L, Commute x u) (hu2 : u * u = 1)
    {g : H} (hg : (g : G) ∈ Subgroup.normalizer (L : Set G)) :
    (g : G) ∈ L ∨ (u : G) * g ∈ L := by
  have hconj : ∀ g' : H, (g' : G) ∈ Subgroup.normalizer (L : Set G) →
      ∀ y ∈ O, ρ g' * y * (ρ g')⁻¹ ∈ O := by
    intro g' hg' y hy
    obtain ⟨x, hx, rfl⟩ := (himg y).mp hy
    refine (himg _).mpr ⟨g' * x * g'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hg' _).mp hx
  have hgN : ρ g ∈ Subgroup.normalizer (O : Set S) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hconj g hg y, fun hy => ?_⟩
    have hg' : ((g⁻¹ : H) : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hg
    have h1 := hconj g⁻¹ hg' _ hy
    rwa [map_inv, inv_inv, show (ρ g)⁻¹ * (ρ g * y * (ρ g)⁻¹) * ρ g = y by group] at h1
  rw [hO] at hgN
  obtain ⟨x, hx, hxg⟩ := (himg _).mp hgN
  have h1 : ρ (x⁻¹ * g) = 1 := by rw [map_mul, map_inv, hxg, inv_mul_cancel]
  rcases hker _ h1 with h2 | h2
  · left
    rw [inv_mul_eq_one] at h2
    rw [← h2]
    exact hx
  · right
    have h3 : g = x * u := by rw [← h2, mul_inv_cancel_left]
    rw [h3]
    change (u : G) * ((x : G) * u) ∈ _
    rw [← mul_assoc, ← (hLu _ hx).eq, mul_assoc,
      show (u : G) * u = 1 from congrArg Subtype.val hu2, mul_one]
    exact hx

end Generic

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem twelveTen_sp_center (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) :
    ∃ hu : hC.d ∈ Halpha D hC.alpha,
      Subgroup.center (Halpha D hC.alpha) = Subgroup.zpowers ⟨hC.d, hu⟩ ∧
      Subgroup.center (Halpha D hC.alpha) ⊓ commutator (Halpha D hC.alpha) = ⊥ ∧
      ∀ x ∈ DstarH hC, x * ⟨hC.d, hu⟩ ∈ commutator (Halpha D hC.alpha) := by
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨hb1, hne⟩ :=
    subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs h
  have htri := isRootTriple_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs hm hf h
  obtain ⟨htop, hmult⟩ := commutator_eq_top_and_ker_eq_bot_of_isSymplecticTransvection hZ hm hf h
  have hperf : ⁅commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))⁆ =
        commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) := by
    rw [htop, ← commutator_def, htop]
  have hmult' : ∀ (Γ : Type) [Group Γ] [Finite Γ]
      (φ : Γ →* ↥(commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → φ.ker = ⊥ :=
    fun Γ _ _ φ => ker_eq_bot_of_commutator_eq_top htop hmult Γ φ
  have hodd : Odd (Nat.card ↥(Subgroup.center (Halpha D hC.alpha) ⊓
      commutator (Halpha D hC.alpha))) :=
    odd_card_center_inf_commutator_of_multiplier hC hMZ hperf (fun Γ _ _ φ hφ hcen hcomm => by
      rw [hmult' Γ φ hφ hcen hcomm, Subgroup.card_bot]
      exact odd_one)
  have hdH := d_mem_Halpha_of_isRootTriple hC hMZ hs hb1 hne htri hodd
  obtain ⟨hdH', hdZ⟩ := mem_center_of_mem_alpha hC hdH hC.d_mem_alpha
  obtain ⟨x₀, hx₀⟩ := DstarH_nonempty hC
  have hMeq : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha) :=
    le_antisymm hMZ (center_le_solvableRadical _)
  have hbot : Subgroup.center (Halpha D hC.alpha) ⊓ commutator (Halpha D hC.alpha) = ⊥ := by
    have h1 := inf_commutator_eq_bot_of_multiplier hMZ
      ((DstarH_isOddTransp hC).mul_self_eq_one hx₀)
      (mem_commutator_or_mul_mem_of_mem_DstarH hC hx₀) hperf hmult'
    rwa [hMeq] at h1
  set u : Halpha D hC.alpha := ⟨hC.d, hdH'⟩ with hudef
  have hu1 : u ≠ 1 := (mul_self_eq_one_and_ne_one_of_mem_alpha hC hC.d_mem_alpha hdH').2
  have huH' : u ∉ commutator (Halpha D hC.alpha) := fun h1 => hu1 (by
    have h2 : u ∈ Subgroup.center (Halpha D hC.alpha) ⊓ commutator (Halpha D hC.alpha) :=
      ⟨hdZ, h1⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact h2)
  have hxu : ∀ x ∈ DstarH hC, x * u ∈ commutator (Halpha D hC.alpha) := fun x hx =>
    (mem_commutator_or_mul_mem_of_mem_DstarH hC hx u).resolve_left huH'
  exact ⟨hdH', center_eq_zpowers_of_inf_eq_bot hbot hdZ
    (mem_commutator_or_mul_mem_of_mem_DstarH hC hx₀) (hxu x₀ hx₀), hbot, hxu⟩

@[expose] def IsMarkedComponentSp (hC : HypothesisC D) (f : ℕ) (Γ : Set G) : Prop :=
  ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = 2 ^ f)
    (e : ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ⧸
        Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) ≃*
      StatedSp k F)
    (Q : (Fin k ⊕ Fin k → F) → F),
    IsSpQuadForm Q ∧
      (fun x : Halpha D hC.alpha => e (QuotientGroup.mk (QuotientGroup.mk x))) ''
          {x | (x : G) ∈ Subgroup.closure Γ} = (spOrthSubgroup Q : Set (StatedSp k F))

private theorem mem_or_mul_mem_of_mem_normalizer_hypLineGroup (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hdH : hC.d ∈ Halpha D hC.alpha)
    (hZ : Subgroup.center (Halpha D hC.alpha) = Subgroup.zpowers ⟨hC.d, hdH⟩) {f : ℕ}
    (hf : 2 ≤ f) {w : G} (hmark : IsMarkedComponentSp hC f (commSet D hC.d ∩ commSet D w))
    {g : G} (hg : g ∈ Halpha D hC.alpha)
    (hgN : g ∈ Subgroup.normalizer (hypLineGroup D hC.d w : Set G)) :
    g ∈ hypLineGroup D hC.d w ∨ hC.d * g ∈ hypLineGroup D hC.d w := by
  classical
  obtain ⟨k, F, _, _, _, hF, e, Q, hQ, himg⟩ := hmark
  set u : Halpha D hC.alpha := ⟨hC.d, hdH⟩ with hudef
  have hu2 : u * u = 1 := (mul_self_eq_one_and_ne_one_of_mem_alpha hC hC.d_mem_alpha hdH).1
  set ρ : Halpha D hC.alpha →* StatedSp k F :=
    e.toMonoidHom.comp ((QuotientGroup.mk' _).comp (QuotientGroup.mk' _)) with hρ
  have hρapp : ∀ x : Halpha D hC.alpha,
      ρ x = e (QuotientGroup.mk (QuotientGroup.mk x)) := fun _ => rfl
  have hker : ∀ z : Halpha D hC.alpha, ρ z = 1 → z = 1 ∨ z = u := by
    intro z hz
    rw [hρapp, map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff,
      center_Hbar_eq_bot hC, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz
    have h1 := hMZ hz
    rw [hZ] at h1
    exact (mem_zpowers_of_mul_self hu2).mp h1
  have himg' : ∀ y, y ∈ spOrthSubgroup Q ↔
      ∃ x : Halpha D hC.alpha, (x : G) ∈ hypLineGroup D hC.d w ∧ ρ x = y := by
    intro y
    rw [← SetLike.mem_coe, ← himg]
    rfl
  have hF2 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hLd : hypLineGroup D hC.d w ≤ Subgroup.centralizer {hC.d} :=
    (Subgroup.closure_le _).mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr hx.1.2.1.eq
  exact mem_or_mul_mem_of_mem_normalizer_of_image (g := ⟨g, hg⟩)
    (hQ.normalizer_spOrthSubgroup hF2) himg' hker
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hLd hx)) hu2 hgN

theorem twelveTen_sp_stabilizers (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s)
    {w : G} (hwd : ¬ Commute w hC.d)
    (hmark : IsMarkedComponentSp hC f (commSet D hC.d ∩ commSet D w)) :
    (∀ g ∈ Halpha D hC.alpha, g ∈ Subgroup.normalizer (hypLineGroup D hC.d w : Set G) →
      g ∈ hypLineGroup D hC.d w ∨ hC.d * g ∈ hypLineGroup D hC.d w) ∧
    Halpha D hC.alpha ⊓ Subgroup.centralizer {w} = hypLineGroup D hC.d w := by
  classical
  obtain ⟨hdH, hZ, -, -⟩ := twelveTen_sp_center hC hMZ hs hm hf h
  have hα := alpha_eq_singleton_of_isSymplecticTransvection hC hMZ hs hm hf h
  have hstar := DalphaStar_eq_commSet_of_alpha_eq hC hα
  have hN : IsNormalSet D := hC.setup.normal
  set Γ := commSet D hC.d ∩ commSet D w with hΓdef
  have hLH : hypLineGroup D hC.d w ≤ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure (by rw [hstar]; exact hx.1)
  have hLw : hypLineGroup D hC.d w ≤ Subgroup.centralizer {w} :=
    (Subgroup.closure_le _).mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr hx.2.2.1.eq
  have key := fun (g : G) (hg : g ∈ Halpha D hC.alpha) =>
    mem_or_mul_mem_of_mem_normalizer_hypLineGroup hC hMZ hdH hZ hf hmark hg
  refine ⟨key, le_antisymm ?_ (le_inf hLH hLw)⟩
  rintro g ⟨hgH, hgw⟩
  have hgw' : Commute g w := Subgroup.mem_centralizer_singleton_iff.mp hgw
  have hgd : Commute g hC.d := Subgroup.mem_centralizer_singleton_iff.mp
    (Halpha_le_centralizer_of_mem_alpha hC hC.d_mem_alpha hgH)
  have hconjL : ∀ a : G, Commute a hC.d → Commute a w →
      ∀ y ∈ hypLineGroup D hC.d w, a * y * a⁻¹ ∈ hypLineGroup D hC.d w := by
    intro a had haw y hy
    have hsub : (MulAut.conj a) '' Γ ⊆ Γ := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨conj_mem_commSet_of_commute hN had hx.1, conj_mem_commSet_of_commute hN haw hx.2⟩
    have hmap : (hypLineGroup D hC.d w).map (MulAut.conj a).toMonoidHom ≤
        hypLineGroup D hC.d w := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono hsub
    exact hmap ⟨y, hy, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (hypLineGroup D hC.d w : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hconjL g hgd hgw' y, fun hy => ?_⟩
    have h1 := hconjL g⁻¹ hgd.inv_left hgw'.inv_left _ hy
    rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  rcases key g hgH hgN with h1 | h1
  · exact h1
  · exfalso
    apply hwd
    have h2 : Commute (hC.d * g) w := Subgroup.mem_centralizer_singleton_iff.mp (hLw h1)
    have h3 : Commute (hC.d * g * g⁻¹) w := h2.mul_left hgw'.inv_left
    rw [mul_inv_cancel_right] at h3
    exact h3.symm

end CFSG.OddTranspositions.PartThree

end
