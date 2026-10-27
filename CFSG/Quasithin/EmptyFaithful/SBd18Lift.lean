module

public import CFSG.Quasithin.EmptyFaithful.SBd14LieG

public section

namespace CFSG.Quasithin.SBd18

open scoped commutatorElement

theorem exists_threeSubgroup {H P : Type} [Group H] [Finite H] [Group P]
    (ρ : H →* P) (hsurj : Function.Surjective ρ)
    (hZc : ∀ z ∈ ρ.ker, ∀ h : H, h * z = z * h) (hZ2 : ∀ z ∈ ρ.ker, z * z = 1)
    (E : Subgroup P) (hE : Nat.card ↥E = 9)
    (hCE : ∀ p : P, (∀ e ∈ E, p * e = e * p) → p ∈ E)
    (ψ : MulAut H) (α : MulAut P) (hψα : ∀ x, α (ρ x) = ρ (ψ x)) (hαE : ∀ e ∈ E, α e = e) :
    ∃ F : Subgroup H, IsPGroup 3 ↥F ∧ Nat.card ↥F = 9 ∧ (∀ x ∈ F, ψ x = x) ∧
      (∀ l : H, (∀ x ∈ F, l * x = x * l) → ∃ f₀ ∈ F, ∃ z ∈ ρ.ker, l = f₀ * z) := by
  classical
  set L₀ : Subgroup H := E.comap ρ with hL₀
  have hkerL₀ : ρ.ker ≤ L₀ := fun z hz => by
    rw [hL₀, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact E.one_mem
  let ρ₀ : ↥L₀ →* ↥E := (ρ.comp L₀.subtype).codRestrict E (fun x => x.2)
  have hρ₀s : Function.Surjective ρ₀ := by
    intro e
    obtain ⟨x, hx⟩ := hsurj (e : P)
    refine ⟨⟨x, by rw [hL₀, Subgroup.mem_comap, hx]; exact e.2⟩, ?_⟩
    exact Subtype.ext hx
  set K₀ : Subgroup ↥L₀ := ρ.ker.subgroupOf L₀ with hK₀
  have hρ₀k : ρ₀.ker = K₀ := by
    ext x
    simp only [MonoidHom.mem_ker, hK₀, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  have : K₀.Normal := Subgroup.Normal.subgroupOf (MonoidHom.normal_ker ρ) L₀
  have hidx : K₀.index = 9 := by
    rw [← hρ₀k, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ₀s, Subgroup.card_top, hE]
  have hK₂ : IsPGroup 2 ↥K₀ := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have := hZ2 (x.1 : H) x.2
    simpa [pow_two] using this
  have hcop : Nat.Coprime (Nat.card ↥K₀) K₀.index := by
    obtain ⟨m, hm⟩ := hK₂.exists_card_eq
    rw [hm, hidx]
    exact Nat.Coprime.pow_left m (by norm_num)
  obtain ⟨F₀, hF₀⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hF₀card : Nat.card ↥F₀ = 9 := by
    have h1 := hF₀.card_mul_card
    have h2 := Subgroup.card_mul_index K₀
    rw [hidx] at h2
    have hpos : 0 < Nat.card ↥K₀ := Nat.card_pos
    have : Nat.card ↥K₀ * Nat.card ↥F₀ = Nat.card ↥K₀ * 9 := by rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hF₀3 : IsPGroup 3 ↥F₀ := IsPGroup.of_card (n := 2) (by rw [hF₀card]; norm_num)
  have hmemF : ∀ y : H, y ∈ F₀.map L₀.subtype ↔ ∃ x : ↥L₀, x ∈ F₀ ∧ (x : H) = y := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hF3pow : ∀ a : H, a ∈ F₀.map L₀.subtype → ∃ k : ℕ, a ^ (3 ^ k) = 1 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (hmemF a).mp ha
    obtain ⟨k, hk⟩ := hF₀3 ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have := congrArg (fun w : ↥F₀ => ((w : ↥L₀) : H)) hk
    simpa using this
  refine ⟨F₀.map L₀.subtype, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨k, hk⟩ := hF3pow y.1 y.2
    exact ⟨k, Subtype.ext hk⟩
  · rw [Subgroup.card_map_of_injective L₀.subtype_injective, hF₀card]
  · intro a ha
    obtain ⟨k, hk⟩ := hF3pow a ha
    obtain ⟨x, hx, rfl⟩ := (hmemF a).mp ha
    have hρa : ρ (x : H) ∈ E := x.2
    have hz : ψ (x : H) * (x : H)⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hψα, hαE _ hρa, mul_inv_cancel]
    set z : H := ψ (x : H) * (x : H)⁻¹ with hzdef
    have hψz : ψ (x : H) = z * (x : H) := by rw [hzdef]; group
    have hc : Commute z (x : H) := (hZc z hz (x : H)).symm
    have h1 : (ψ (x : H)) ^ (3 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    rw [hψz, hc.mul_pow, hk, mul_one] at h1
    obtain ⟨m, hm⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
    have hz1 : z = 1 := by
      have hz2 := hZ2 z hz
      rw [hm, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul] at h1
      exact h1
    rw [hψz, hz1, one_mul]
  · intro l hl
    have hinj : Function.Injective (fun x : ↥F₀ => ρ₀ (x : ↥L₀)) := by
      intro x y hxy
      have h1 : ρ₀ ((x : ↥L₀)⁻¹ * (y : ↥L₀)) = 1 := by
        rw [map_mul, map_inv]
        simp only at hxy
        rw [hxy, inv_mul_cancel]
      have h2 : (x : ↥L₀)⁻¹ * (y : ↥L₀) ∈ K₀ := by rw [← hρ₀k]; exact h1
      have h3 : (x : ↥L₀)⁻¹ * (y : ↥L₀) ∈ F₀ := F₀.mul_mem (F₀.inv_mem x.2) y.2
      have h4 : (x : ↥L₀)⁻¹ * (y : ↥L₀) = 1 := Subgroup.disjoint_def.mp hF₀.disjoint h2 h3
      exact Subtype.ext (inv_mul_eq_one.mp h4)
    have hfinE : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
    have hbij := hinj.bijective_of_nat_card_le (by rw [hE, hF₀card])
    have hEF : ∀ e ∈ E, ∃ x : ↥L₀, x ∈ F₀ ∧ ρ (x : H) = e := by
      intro e he
      obtain ⟨x, hx⟩ := hbij.2 ⟨e, he⟩
      exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
    have hρl : ρ l ∈ E := by
      refine hCE (ρ l) fun e he => ?_
      obtain ⟨x, hxF, hxe⟩ := hEF e he
      have h1 := hl (x : H) ((hmemF _).mpr ⟨x, hxF, rfl⟩)
      rw [← hxe, ← map_mul, ← map_mul, h1]
    have hlL₀ : l ∈ L₀ := hρl
    obtain ⟨⟨k, f⟩, hkf, -⟩ := (Subgroup.isComplement_iff_existsUnique.mp hF₀) (⟨l, hlL₀⟩ : ↥L₀)
    have hkker : ((k : ↥L₀) : H) ∈ ρ.ker := Subgroup.mem_subgroupOf.mp k.2
    refine ⟨((f : ↥L₀) : H), (hmemF _).mpr ⟨f, f.2, rfl⟩, ((k : ↥L₀) : H), hkker, ?_⟩
    have h1 : ((k : ↥L₀) : H) * ((f : ↥L₀) : H) = l := congrArg Subtype.val hkf
    rw [← h1]
    exact (hZc _ hkker _).symm


theorem perfect_core {H P : Type} [Group H] [Group P]
    (ρ : H →* P) (hsurj : Function.Surjective ρ) (hZc : ∀ z ∈ ρ.ker, ∀ h : H, h * z = z * h)
    (ψ : MulAut H) (α : MulAut P) (hψα : ∀ x, α (ρ x) = ρ (ψ x))
    (A : Subgroup P) (hAfix : ∀ p ∈ A, α p = p) (hAperf : ⁅A, A⁆ = A) :
    ⁅⁅A.comap ρ, A.comap ρ⁆, ⁅A.comap ρ, A.comap ρ⁆⁆ = ⁅A.comap ρ, A.comap ρ⁆ ∧
      (∀ x ∈ ⁅A.comap ρ, A.comap ρ⁆, ψ x = x) ∧ (∀ x ∈ ⁅A.comap ρ, A.comap ρ⁆, ρ x ∈ A) ∧
      (∀ p ∈ A, ∃ x ∈ ⁅A.comap ρ, A.comap ρ⁆, ρ x = p) := by
  classical
  set H₀ : Subgroup H := A.comap ρ with hH₀
  set K : Subgroup H := ⁅H₀, H₀⁆ with hK
  have hcomm_mem : ∀ g₁ ∈ H₀, ∀ g₂ ∈ H₀, ⁅g₁, g₂⁆ ∈ H₀ := by
    intro g₁ hg₁ g₂ hg₂
    rw [hH₀, Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem (Subgroup.mem_comap.mp hg₁) (Subgroup.mem_comap.mp hg₂))
      (A.inv_mem (Subgroup.mem_comap.mp hg₁))) (A.inv_mem (Subgroup.mem_comap.mp hg₂))
  have hKH₀ : K ≤ H₀ := Subgroup.commutator_le.mpr hcomm_mem
  have hρK : K.map ρ = A := by
    rw [hK, Subgroup.map_commutator, hH₀, Subgroup.map_comap_eq_self_of_surjective hsurj A, hAperf]
  have hcover : ∀ p ∈ A, ∃ x ∈ K, ρ x = p := by
    intro p hp
    rw [← hρK] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact ⟨x, hx, rfl⟩
  have hfix : K ≤ (ψ.toMonoidHom).eqLocus (MonoidHom.id H) := by
    rw [hK, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have key : ∀ g ∈ H₀, ∃ z ∈ ρ.ker, ψ g = g * z := by
      intro g hg
      have hρg : ρ g ∈ A := Subgroup.mem_comap.mp hg
      refine ⟨g⁻¹ * ψ g, ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hψα, hAfix _ hρg, inv_mul_cancel]
    obtain ⟨z₁, hz₁, h1⟩ := key g₁ hg₁
    obtain ⟨z₂, hz₂, h2⟩ := key g₂ hg₂
    show ψ ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
    rw [map_commutatorElement, h1, h2]
    exact SBd14.commutator_mul_central (hZc z₁ hz₁ g₂).symm (hZc z₂ hz₂ z₁)
      (hZc z₂ hz₂ g₁).symm
  have hperf : ⁅K, K⁆ = K := by
    apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    · show ⁅H₀, H₀⁆ ≤ ⁅K, K⁆
      refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
      obtain ⟨k₁, hk₁, hk₁ρ⟩ := hcover (ρ g₁) (Subgroup.mem_comap.mp hg₁)
      obtain ⟨k₂, hk₂, hk₂ρ⟩ := hcover (ρ g₂) (Subgroup.mem_comap.mp hg₂)
      have hz₁ : k₁⁻¹ * g₁ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hk₁ρ, inv_mul_cancel]
      have hz₂ : k₂⁻¹ * g₂ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hk₂ρ, inv_mul_cancel]
      have e₁ : g₁ = k₁ * (k₁⁻¹ * g₁) := by group
      have e₂ : g₂ = k₂ * (k₂⁻¹ * g₂) := by group
      have hc : ⁅g₁, g₂⁆ = ⁅k₁, k₂⁆ := by
        rw [e₁, e₂]
        exact SBd14.commutator_mul_central (hZc _ hz₁ k₂).symm (hZc _ hz₂ _) (hZc _ hz₂ k₁).symm
      rw [hc]
      exact Subgroup.commutator_mem_commutator hk₁ hk₂
  exact ⟨hperf, fun x hx => hfix hx, fun x hx => Subgroup.mem_comap.mp (hKH₀ hx), hcover⟩

theorem isQuasisimple_core {H P : Type} [Group H] [Group P]
    (ρ : H →* P) (hsurj : Function.Surjective ρ) (hZc : ∀ z ∈ ρ.ker, ∀ h : H, h * z = z * h)
    (ψ : MulAut H) (α : MulAut P) (hψα : ∀ x, α (ρ x) = ρ (ψ x))
    (A : Subgroup P) (hAfix : ∀ p ∈ A, α p = p) (hAperf : ⁅A, A⁆ = A)
    (hAsimple : IsSimpleGroup ↥A) (hAnc : ∃ a b : ↥A, a * b ≠ b * a) :
    CFSG.IsQuasisimple ↥⁅A.comap ρ, A.comap ρ⁆ ∧
      (∀ z ∈ Subgroup.center ↥⁅A.comap ρ, A.comap ρ⁆,
        ρ ((z : ↥⁅A.comap ρ, A.comap ρ⁆) : H) = 1) ∧
      Nat.card (↥⁅A.comap ρ, A.comap ρ⁆ ⧸ Subgroup.center ↥⁅A.comap ρ, A.comap ρ⁆) =
        Nat.card ↥A := by
  classical
  obtain ⟨hperf, -, hKA, hcover⟩ := perfect_core ρ hsurj hZc ψ α hψα A hAfix hAperf
  set K : Subgroup H := ⁅A.comap ρ, A.comap ρ⁆ with hK
  let f : ↥K →* ↥A := (ρ.comp K.subtype).codRestrict A (fun x => hKA x.1 x.2)
  have hfs : Function.Surjective f := by
    intro p
    obtain ⟨x, hx, hxp⟩ := hcover p.1 p.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxp⟩
  have hfker : ∀ x : ↥K, x ∈ f.ker ↔ ρ (x : H) = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcentral : f.ker ≤ Subgroup.center ↥K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hZc _ ((hfker x).mp hx) y)
  let e : (↥K ⧸ f.ker) ≃* ↥A := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hsimpleQ : IsSimpleGroup (↥K ⧸ f.ker) := e.isSimpleGroup
  have hnc : ∃ a b : ↥K ⧸ f.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hAnc
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have hq : CFSG.IsQuasisimple ↥K :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient f.ker hcentral
      (Subgroup.isPerfect_iff.mpr hperf) hsimpleQ hnc
  have hcenA : Subgroup.center ↥A = ⊥ := by
    rcases hAsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hAnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hcenK : Subgroup.center ↥K = f.ker := by
    have h1 := CFSG.LocalCores.comap_center_eq_of_perfect (Subgroup.isPerfect_iff.mpr hperf) f hfs
      hcentral
    rw [hcenA, MonoidHom.comap_bot] at h1
    exact h1.symm
  refine ⟨hq, fun z hz => ?_, ?_⟩
  · rw [hcenK] at hz
    exact (hfker z).mp hz
  · rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcenK).toEquiv]
    exact Nat.card_congr e.toEquiv

theorem simple_nonabelian_of_card {P : Type} [Group P] (A : Subgroup P) [Finite ↥A]
    (hs : IsSimpleGroup ↥A) (hp : ¬ (Nat.card ↥A).Prime) :
    (∃ a b : ↥A, a * b ≠ b * a) ∧ ⁅A, A⁆ = A := by
  have hnc : ∃ a b : ↥A, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hcon }
    exact hp (IsSimpleGroup.prime_card (α := ↥A))
  refine ⟨hnc, ?_⟩
  have hcomm : commutator ↥A = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥A) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator ↥A :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hcomm)

theorem card_quot_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) := by
  have hmap : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine Subgroup.mem_center_iff.mpr fun b => ?_
      obtain ⟨b', rfl⟩ := e.surjective b
      have := congrArg e (Subgroup.mem_center_iff.mp ha b')
      simpa [map_mul] using this
    · intro hz
      refine ⟨e.symm z, Subgroup.mem_center_iff.mpr fun a => ?_, by simp⟩
      apply e.injective
      have := Subgroup.mem_center_iff.mp hz (e a)
      simpa [map_mul] using this
  exact Nat.card_congr
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hmap).toEquiv

end CFSG.Quasithin.SBd18
