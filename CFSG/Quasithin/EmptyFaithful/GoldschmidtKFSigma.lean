module

public import CFSG.Quasithin.EmptyFaithful.SBd18Cl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSolv
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_sigma_structure (r : RestHyp T Mc M V₁ V₂ Yp I L t)
    (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    {τ σ : G} (hτS : τ ∈ Sgp153 T V₁) (hτ2 : τ * τ = 1) (hτm : ∃ v ∈ V₁, τ * v ≠ v * τ)
    (hσS : σ ∈ Sgp153 T V₁) (hσ2 : σ * σ = 1) (hσc : ∀ v ∈ V₁, σ * v = v * σ) (hσL : σ ∉ L) :
    ∃ F : Subgroup G, F ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card ↥F = 9 ∧
      (∀ x ∈ F, σ * x = x * σ) ∧
      (∀ l ∈ L, σ * l = l * σ → Odd (orderOf l) → l ∈ F) ∧
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({σ} : Set G)) := by
  classical
  obtain ⟨K, _, _, _, ρ, φ, Φ, Ψ, hK4, hsurj, hker, hφ, hΦ, hΘker, hΘs, hcls, -, -⟩ :=
    r.exists_outer_setup h113 hOut hτS hτ2 hτm hσS hσ2 hσc hσL
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hσI : σ ∈ I := r.S_le_I hσS
  set s : ↥I := ⟨σ, hσI⟩ with hs
  have hss : s * s = 1 := Subtype.ext hσ2
  have hΦss : Φ s * Φ s = 1 := by rw [← map_mul, hss, map_one]
  have hright : (Ψ (Φ s)).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
    have : Ψ (Φ s) = SBd18.OutGrp.z₀ K := hΘs
    rw [this]
    rfl
  obtain ⟨E, hE9, hEfix, hN, hCE⟩ := (hcls (Φ s) hΦss).2.2.2 hright
  have hCEgen : ∀ p : projectiveSL 3 K, (∀ e ∈ E, p * e = e * p) → p ∈ E := by
    obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : E = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [this, Subgroup.card_bot] at hE9
      omega
    intro p hp
    have hp' : p ∈ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hp x hxE)
    rwa [hCE x hxE hx1] at hp'
  have hZc : ∀ z ∈ ρ.ker, ∀ h : ↥L, h * z = z * h := by
    intro z hz h
    rw [hker] at hz
    exact (Subgroup.mem_center_iff.mp hz h)
  have hZ2 : ∀ z ∈ ρ.ker, z * z = 1 := by
    intro z hz
    rw [hker] at hz
    have hzV : (z : G) ∈ V₁ := by
      rw [hV₁]
      exact SBd9.mem_centerOf_iff.mpr hz
    exact Subtype.ext (r.V_sq _ (r.ctx.hyp.decomp.le₁ hzV))
  obtain ⟨F₀, hF₀3, hF₀9, hF₀fix, -⟩ := SBd18.exists_threeSubgroup ρ hsurj hZc hZ2 E hE9
    hCEgen (φ s) (Φ s) (fun x => hΦ s x) hEfix
  have hoddE : ∀ q : projectiveSL 3 K, q ∈ SBd18.fixedSub (Φ s) → Odd (orderOf q) → q ∈ E := by
    intro q hq hodd
    rw [hN] at hq
    exact SBd19F.mem_of_odd_orderOf_of_mem_normalizer hE9 hCE hq hodd
  have hkerodd : ∀ z ∈ ρ.ker, Odd (orderOf z) → z = 1 := by
    intro z hz hodd
    have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hZ2 z hz)
    have h1 : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  have hinj : ∀ x ∈ F₀, ρ x = 1 → x = 1 := by
    intro x hx hρ
    obtain ⟨k, hk⟩ := hF₀3 ⟨x, hx⟩
    have hk' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact hkerodd x hρ (by
      have : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
      exact Odd.of_dvd_nat (Odd.pow (by decide)) this)
  have hρF : ∀ x ∈ F₀, ρ x ∈ E := by
    intro x hx
    have hfix : ρ x ∈ SBd18.fixedSub (Φ s) := by
      rw [SBd18.mem_fixedSub, hΦ s x, hF₀fix x hx]
    obtain ⟨k, hk⟩ := hF₀3 ⟨x, hx⟩
    have hk' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf (ρ x)) := by
      have hd : orderOf (ρ x) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
      exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
    exact hoddE _ hfix hodd
  have hρFonto : ∀ e ∈ E, ∃ x ∈ F₀, ρ x = e := by
    let g : ↥F₀ →* ↥E := (ρ.comp F₀.subtype).codRestrict E (fun x => hρF x.1 x.2)
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have : ρ (x : ↥L) = 1 := congrArg Subtype.val hx
      exact Subtype.ext (hinj x x.2 this)
    have hgbij : Function.Bijective g :=
      hginj.bijective_of_nat_card_le (by rw [hE9, hF₀9])
    intro e he
    obtain ⟨x, hx⟩ := hgbij.2 ⟨e, he⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hEel := CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_of_card_eq_nine hK4 hE9
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := fun e he => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEel.exponent_dvd_p ⟨e, he⟩
    simpa using congrArg Subtype.val this
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have := hEel.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ a ∈ F₀, ∀ b ∈ F₀, a * b = b * a := by
    intro a ha b hb
    have hc : a * b * (b * a)⁻¹ ∈ F₀ :=
      F₀.mul_mem (F₀.mul_mem ha hb) (F₀.inv_mem (F₀.mul_mem hb ha))
    have h1 : ρ (a * b * (b * a)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hEcomm _ (hρF a ha) _ (hρF b hb), mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj _ hc h1)
  have hcube : ∀ a ∈ F₀, a ^ 3 = 1 := fun a ha =>
    hinj _ (F₀.pow_mem ha 3) (by rw [map_pow]; exact hE3 _ (hρF a ha))
  refine ⟨F₀.map L.subtype, Subgroup.map_subtype_le F₀, ⟨⟨⟨?_⟩⟩, ?_⟩,
    (Subgroup.card_map_of_injective L.subtype_injective).trans hF₀9, ?_, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have := congrArg (fun w : ↥L => (w : G)) (hcomm a ha b hb)
    exact Subtype.ext this
  · rintro _ ⟨a, ha, rfl⟩
    have := congrArg Subtype.val (hcube a ha)
    simpa using this
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := hφ s y
    rw [hF₀fix y hy] at h1
    have h2 : (y : G) = σ * (y : G) * σ⁻¹ := h1
    calc σ * (y : G) = (σ * (y : G) * σ⁻¹) * σ := by group
      _ = (y : G) * σ := by rw [← h2]
  · intro l hl hσl hodd
    set l' : ↥L := ⟨l, hl⟩ with hl'
    have hfix : ρ l' ∈ SBd18.fixedSub (Φ s) := by
      rw [SBd18.mem_fixedSub, hΦ s l']
      congr 1
      apply Subtype.ext
      rw [hφ s l']
      change σ * l * σ⁻¹ = l
      rw [hσl]
      group
    have hoddρ : Odd (orderOf (ρ l')) := by
      have hd : orderOf (ρ l') ∣ orderOf l' := orderOf_map_dvd ρ l'
      have h2 : orderOf l' = orderOf l := (Subgroup.orderOf_coe l').symm
      rw [h2] at hd
      exact Odd.of_dvd_nat hodd hd
    obtain ⟨f, hfF, hfρ⟩ := hρFonto _ (hoddE _ hfix hoddρ)
    have hz : f⁻¹ * l' ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfρ, inv_mul_cancel]
    have hcf : Commute f l' := by
      have h := hZc _ hz f
      rw [mul_inv_cancel_left] at h
      change f * l' = l' * f
      calc f * l' = f * (f⁻¹ * l' * f) := by rw [← h]
        _ = l' * f := by group
    obtain ⟨k, hk⟩ := hF₀3 ⟨f, hfF⟩
    have hfk : f ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hodd' : Odd (orderOf (f⁻¹ * l')) := by
      have h1 : Odd (orderOf f⁻¹) := by
        rw [orderOf_inv]
        exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hfk)
      have h2 : Odd (orderOf l') := by
        have : orderOf l' = orderOf l := (Subgroup.orderOf_coe l').symm
        rw [this]
        exact hodd
      have hd := (hcf.inv_left).orderOf_mul_dvd_lcm
      exact Odd.of_dvd_nat (Odd.of_dvd_nat (h1.mul h2) (Nat.lcm_dvd_mul _ _)) hd
    have hz1 : f⁻¹ * l' = 1 := hkerodd _ hz hodd'
    have hl'f : l' = f := by
      have := congrArg (f * ·) hz1
      simpa using this
    refine ⟨f, hfF, ?_⟩
    have := congrArg (fun w : ↥L => (w : G)) hl'f
    exact this.symm
  · let incl : ↥(L ⊓ Subgroup.centralizer ({σ} : Set G)) →* ↥L :=
      Subgroup.inclusion inf_le_left
    let ι₀ : ↥(L ⊓ Subgroup.centralizer ({σ} : Set G)) →* projectiveSL 3 K := ρ.comp incl
    have hι : ∀ x, ι₀ x ∈ SBd18.fixedSub (Φ s) := by
      intro x
      rw [SBd18.mem_fixedSub]
      change Φ s (ρ (incl x)) = ρ (incl x)
      rw [hΦ s (incl x)]
      congr 1
      apply Subtype.ext
      rw [hφ s (incl x)]
      have hx : σ * (x : G) = (x : G) * σ :=
        (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm
      change σ * (x : G) * σ⁻¹ = (x : G)
      rw [hx]
      group
    let ι : ↥(L ⊓ Subgroup.centralizer ({σ} : Set G)) →* ↥(SBd18.fixedSub (Φ s)) :=
      ι₀.codRestrict _ hι
    have hsolvN : Group.IsSolvable ↥(SBd18.fixedSub (Φ s)) := by
      rw [hN]
      exact SBd19F.isSolvable_normalizer_of_card_nine hE9 hCE
    have hsolvK : Group.IsSolvable ↥ι.ker := by
      refine Group.isSolvable_of_comm (fun a b => ?_)
      have ha : ρ (incl a.1) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
      have ha' : incl a.1 ∈ ρ.ker := MonoidHom.mem_ker.mpr ha
      apply Subtype.ext
      apply Subgroup.inclusion_injective (inf_le_left : L ⊓ Subgroup.centralizer ({σ} : Set G) ≤ L)
      change incl (a.1 * b.1) = incl (b.1 * a.1)
      rw [map_mul, map_mul]
      exact (hZc _ ha' (incl b.1)).symm
    exact Group.isSolvable_of_ker_le_range ι.ker.subtype ι (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

end CFSG.Quasithin.SBd14
