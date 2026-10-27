module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeJ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallElem
import CFSG.Quasithin.Background.HSecQuot
import CFSG.GH74.E2.CaseIStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Small

theorem commutator_mem_of_fixed_mod {Hh : Type} [Group Hh] [Finite Hh] {W V₀ : Subgroup Hh}
    (hW : IsElemAbelian 2 W) (hV₀W : V₀ ≤ W) (hcard : Nat.card W = 4 * Nat.card V₀) {c : Hh}
    (hc : c ^ 3 = 1) (hcW : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hcV₀ : ∀ w ∈ V₀, c * w * c⁻¹ ∈ V₀) {a : Hh} (ha : a ∈ W) (haV₀ : a ∉ V₀)
    (hfix : c * a * c⁻¹ * a⁻¹ ∈ V₀) : ∀ w ∈ W, c * w * c⁻¹ * w⁻¹ ∈ V₀ := by
  classical
  have hc' : c * (c * c) = 1 := by rw [← pow_three]; exact hc
  have hcn : ∀ S : Subgroup Hh, (∀ w ∈ S, c * w * c⁻¹ ∈ S) → c ∈ normalizer (S : Set Hh) := by
    intro S hS
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hS h, fun hh => ?_⟩
    have e : h = c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ := by
      have : c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * h * (c * (c * c))⁻¹ := by
        group
      rw [this, hc']
      group
    rw [e]
    exact hS _ (hS _ hh)
  have hcnW : c ∈ normalizer (W : Set Hh) := hcn W hcW
  have hcnV : c ∈ normalizer (V₀ : Set Hh) := hcn V₀ hcV₀
  haveI hNorm : (V₀.subgroupOf W).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : (g : Hh) * n * (g : Hh)⁻¹ = n := by
      have := comm_of_isElemAbelian hW g.2 n.2
      rw [this]
      group
    have h2 : g * n * g⁻¹ = n := Subtype.ext h1
    rw [h2]
    exact hn
  have key : ∀ x y : Hh, x ∈ W → y ∈ W → (x⁻¹ * y ∈ V₀ ↔ x * y⁻¹ ∈ V₀) := by
    intro x y hx hy
    have e : x * y⁻¹ = (x⁻¹ * y)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact comm_of_isElemAbelian hW hx
        (W.inv_mem hy)
    rw [e]
    exact (V₀.inv_mem_iff).symm
  set σ : MulAut (↥W ⧸ V₀.subgroupOf W) := CFSG.Quasithin.H.SecQ.conjW hcnW hcnV with hσ
  have hσmk : ∀ u : ↥W, σ (QuotientGroup.mk u) =
      (QuotientGroup.mk (CFSG.Quasithin.H.SecQ.conjA hcnW u) : ↥W ⧸ V₀.subgroupOf W) :=
    fun u => CFSG.Quasithin.H.SecQ.conjW_mk hcnW hcnV u
  have hσ3 : σ ^ 3 = 1 := by
    ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    have h3 : (σ ^ 3) (QuotientGroup.mk u) = σ (σ (σ (QuotientGroup.mk u))) := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
    rw [h3, hσmk, hσmk, hσmk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only [CFSG.Quasithin.H.SecQ.coe_conjA]
    have : c * (c * (c * (u : Hh) * c⁻¹) * c⁻¹) * c⁻¹ =
        (c * (c * c)) * (u : Hh) * (c * (c * c))⁻¹ := by group
    rw [this, hc']
    group
  have hV₀card : Nat.card (V₀.subgroupOf W) = Nat.card V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀W).toEquiv
  have hq4 : Nat.card (↥W ⧸ V₀.subgroupOf W) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (V₀.subgroupOf W)
    rw [hV₀card, hcard] at h
    have hpos : 0 < Nat.card V₀ := Nat.card_pos
    nlinarith
  have hā : (QuotientGroup.mk (⟨a, ha⟩ : ↥W) : ↥W ⧸ V₀.subgroupOf W) ≠ 1 := by
    intro h
    have := (QuotientGroup.eq_one_iff (N := V₀.subgroupOf W) (⟨a, ha⟩ : ↥W)).1 h
    exact haV₀ (Subgroup.mem_subgroupOf.1 this)
  have hσā : σ (QuotientGroup.mk (⟨a, ha⟩ : ↥W)) = QuotientGroup.mk (⟨a, ha⟩ : ↥W) := by
    rw [hσmk]
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have hx : c * a * c⁻¹ ∈ W := hcW a ha
    have := (key (c * a * c⁻¹) a hx ha).2 (by simpa using hfix)
    simpa [CFSG.Quasithin.H.SecQ.coe_conjA] using this
  have h1 : σ = 1 := CFSG.GH74.E2.eq_one_of_fixed_ne_one hq4 σ hσ3 hā hσā
  intro w hw
  have h2 : σ (QuotientGroup.mk (⟨w, hw⟩ : ↥W)) = QuotientGroup.mk (⟨w, hw⟩ : ↥W) := by
    rw [h1, MulAut.one_apply]
  rw [hσmk] at h2
  have h3 := QuotientGroup.eq.1 h2
  rw [Subgroup.mem_subgroupOf] at h3
  have hx : c * w * c⁻¹ ∈ W := hcW w hw
  exact (key (c * w * c⁻¹) w hx hw).1 (by simpa [CFSG.Quasithin.H.SecQ.coe_conjA] using h3)

theorem exists_orderOf_three_of_stronglyPEmbedded {H M : Subgroup G}
    (hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 ((H ⊓ M).subgroupOf H)) :
    ∃ c : G, c ∈ H ∧ c ∈ M ∧ orderOf c = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (H ⊓ M : Subgroup G) := by
    have h1 := hse.2.1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ M ≤ H)).toEquiv] at h1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨(c : G), (Subgroup.mem_inf.1 c.2).1, (Subgroup.mem_inf.1 c.2).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hc

theorem card_le_four_of_mSub_le_two {V₀ : Subgroup G} (hV₀ : IsPGroup 2 V₀) (h : mSub V₀ ≤ 2) :
    Nat.card V₀ ≤ 4 := by
  rw [card_eq_two_pow_mSub hV₀]
  calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
    _ = 4 := by norm_num

end Small

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem not_le_sup_V₀ (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ V ≤ V₀ ⊔ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  change ¬ V ≤ V₀ ⊔ K
  intro hle
  have hVH : V ≤ H := le_sup_left.trans (h.le_centralizer_of_eq_zpowers hz)
  have hKH : K ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hKN : (K.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hHnormK : H ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKN
  have hV₀norm : V₀ ≤ normalizer (K : Set G) := (h.V₀_le.trans hVH).trans hHnormK
  have hinf : V ⊓ K ≤ V ⊓ conjSubgroup M g := h.inf_relPPrimeCore_le hs hs' hz
  have hV₀U : V₀ ≤ V ⊓ conjSubgroup M g := h.V₀_le_U hs
  have hVU : V ≤ V ⊓ conjSubgroup M g := by
    intro v hv
    have hmem : v ∈ ((V₀ ⊔ K : Subgroup G) : Set G) := hle hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ K hV₀norm] at hmem
    obtain ⟨a, ha, k, hk, rfl⟩ := hmem
    have hkV : k ∈ V := by
      have := V.mul_mem (V.inv_mem (h.V₀_le ha)) hv
      simpa using this
    have hkU : k ∈ V ⊓ conjSubgroup M g := hinf (Subgroup.mem_inf.2 ⟨hkV, hk⟩)
    exact (V ⊓ conjSubgroup M g).mul_mem (hV₀U ha) hkU
  have h1 : (V ⊓ conjSubgroup M g).relIndex V = 1 := Subgroup.relIndex_eq_one.2 hVU
  have h2 : (V ⊓ conjSubgroup M g).relIndex V = 2 := h.relIndex_U hs.1
  omega

theorem commutator_mem_V₀ (h : Cfg1667Ne M V₀ V W₁ W₂) {z c : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hnot : ¬ centralizer ({z} : Set G) ≤ M) (hcM : c ∈ M) (hc3 : c ^ 3 = 1)
    (hcz : c * z = z * c) : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀ := by
  classical
  have hV := h.elemAbelian
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Small.comm_of_isElemAbelian hV ha hb
  have hW₁V : W₁ ≤ V := h.W₁_le
  have hW₂V : W₂ ≤ V := h.W₂_le
  have hV₀V : V₀ ≤ V := h.V₀_le
  have hnormW : W₁ ≤ normalizer (W₂ : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm a (hW₁V ha) b (hW₂V hb)).symm)
  have hdecomp : ∀ v ∈ V, ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = v := by
    intro v hv
    have hv' : v ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by
      rw [h.sup_eq]
      exact hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂ hnormW] at hv'
    obtain ⟨a, ha, b, hb, hab⟩ := hv'
    exact ⟨a, ha, b, hb, hab⟩
  have hzW₁ : z ∉ W₁ := fun hz => hnot (h.centralizer_le z (Or.inl hz) hz1)
  have hzW₂ : z ∉ W₂ := fun hz => hnot (h.centralizer_le z (Or.inr hz) hz1)
  obtain ⟨a₁, ha₁, a₂, ha₂, hz12⟩ := hdecomp z hzV
  have ha₁V₀ : a₁ ∉ V₀ := fun hv => hzW₂ (by
    rw [← hz12]
    exact W₂.mul_mem (h.V₀_le₂ hv) ha₂)
  have ha₂V₀ : a₂ ∉ V₀ := fun hv => hzW₁ (by
    rw [← hz12]
    exact W₁.mul_mem ha₁ (h.V₀_le₁ hv))
  have hc3' : c * (c * c) = 1 := by
    rw [← pow_three]
    exact hc3
  have key : ∀ A B : Subgroup G, conjSubgroup A c = B → conjSubgroup B c = A → A ≤ B := by
    intro A B hAB hBA x hx
    have e1 : c * x * c⁻¹ ∈ B := mem_conjSubgroup_iff.1 (by rw [hBA]; exact hx)
    have e2 : c * (c * x * c⁻¹) * c⁻¹ ∈ A := mem_conjSubgroup_iff.1 (by rw [hAB]; exact e1)
    have e3 : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ ∈ B :=
      mem_conjSubgroup_iff.1 (by rw [hBA]; exact e2)
    have e4 : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * x * (c * (c * c))⁻¹ := by
      group
    rw [e4, hc3'] at e3
    simpa using e3
  have hfix : conjSubgroup W₁ c = W₁ ∧ conjSubgroup W₂ c = W₂ := by
    rcases h.perm c hcM with hp | ⟨h1, h2⟩
    · exact hp
    · exact absurd (le_antisymm (key W₁ W₂ h1 h2) (key W₂ W₁ h2 h1)) h.W₁_ne_W₂
  have hcW₁ : ∀ w ∈ W₁, c * w * c⁻¹ ∈ W₁ := fun w hw =>
    mem_conjSubgroup_iff.1 (by rw [hfix.1]; exact hw)
  have hcW₂ : ∀ w ∈ W₂, c * w * c⁻¹ ∈ W₂ := fun w hw =>
    mem_conjSubgroup_iff.1 (by rw [hfix.2]; exact hw)
  have hcV₀ : ∀ w ∈ V₀, c * w * c⁻¹ ∈ V₀ := fun w hw =>
    (Subgroup.mem_normalizer_iff.1 (h.le_normalizer₀ hcM) w).1 hw
  have hczc : c * z * c⁻¹ = z := by
    rw [hcz]
    group
  have hprod : (c * a₁ * c⁻¹) * (c * a₂ * c⁻¹) = a₁ * a₂ := by
    calc (c * a₁ * c⁻¹) * (c * a₂ * c⁻¹) = c * (a₁ * a₂) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [hz12]
      _ = z := hczc
      _ = a₁ * a₂ := hz12.symm
  have he : a₁⁻¹ * (c * a₁ * c⁻¹) = a₂ * (c * a₂ * c⁻¹)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    calc a₁⁻¹ * (c * a₁ * c⁻¹) * (c * a₂ * c⁻¹) = a₁⁻¹ * ((c * a₁ * c⁻¹) * (c * a₂ * c⁻¹)) := by
          rw [mul_assoc]
      _ = a₂ := by rw [hprod]; group
  have heV₀ : a₁⁻¹ * (c * a₁ * c⁻¹) ∈ V₀ := by
    rw [← h.inf_eq]
    refine Subgroup.mem_inf.2 ⟨W₁.mul_mem (W₁.inv_mem ha₁) (hcW₁ a₁ ha₁), ?_⟩
    rw [he]
    exact W₂.mul_mem ha₂ (W₂.inv_mem (hcW₂ a₂ ha₂))
  have hfix₁ : c * a₁ * c⁻¹ * a₁⁻¹ ∈ V₀ := by
    have h1 : c * a₁ * c⁻¹ = a₁ * (a₁⁻¹ * (c * a₁ * c⁻¹)) := by group
    have h2 := hcomm a₁ (hW₁V ha₁) _ (hV₀V heV₀)
    rw [h1, h2, mul_assoc, mul_inv_cancel, mul_one]
    exact heV₀
  have hfix₂ : c * a₂ * c⁻¹ * a₂⁻¹ ∈ V₀ := by
    have h1 : c * a₂ * c⁻¹ * a₂⁻¹ = (a₁⁻¹ * (c * a₁ * c⁻¹))⁻¹ := by
      rw [he]
      group
    rw [h1]
    exact V₀.inv_mem heV₀
  have hW₁all : ∀ w ∈ W₁, c * w * c⁻¹ * w⁻¹ ∈ V₀ :=
    Small.commutator_mem_of_fixed_mod (Small.isElemAbelian_of_le hV hW₁V) h.V₀_le₁ h.card₁ hc3
      hcW₁ hcV₀ ha₁ ha₁V₀ hfix₁
  have hW₂all : ∀ w ∈ W₂, c * w * c⁻¹ * w⁻¹ ∈ V₀ :=
    Small.commutator_mem_of_fixed_mod (Small.isElemAbelian_of_le hV hW₂V) h.V₀_le₂ h.card₂ hc3
      hcW₂ hcV₀ ha₂ ha₂V₀ hfix₂
  intro v hv
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hdecomp v hv
  have t₁ := hW₁all w₁ hw₁
  have t₂ := hW₂all w₂ hw₂
  have hid : c * (w₁ * w₂) * c⁻¹ * (w₁ * w₂)⁻¹ =
      (c * w₁ * c⁻¹ * w₁⁻¹) * (w₁ * (c * w₂ * c⁻¹ * w₂⁻¹) * w₁⁻¹) := by
    group
  have hcommw : w₁ * (c * w₂ * c⁻¹ * w₂⁻¹) = (c * w₂ * c⁻¹ * w₂⁻¹) * w₁ :=
    hcomm w₁ (hW₁V hw₁) _ (hV₀V t₂)
  rw [hid, hcommw, mul_inv_cancel_right]
  exact V₀.mul_mem t₁ t₂

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
