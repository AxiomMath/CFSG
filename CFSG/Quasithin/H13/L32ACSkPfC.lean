module

public import CFSG.Quasithin.H13.L32ACSkPfA
public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThree.PartTwo.KFacts (centerDescend isInnerAut_of_isInnerAut_centerDescend)

section Lemmas

variable {G : Type} [Group G]

theorem mulAut_apply_mem_center (α : MulAut G) {z : G} (hz : z ∈ Subgroup.center G) :
    α z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h := congrArg α (hz (α.symm g))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem mem_of_sq_mem_of_cube_mem {H : Subgroup G} {g : G} (h2 : g ^ 2 ∈ H) (h3 : g ^ 3 ∈ H) :
    g ∈ H := by
  have h := mul_mem h3 (inv_mem h2)
  rwa [show g ^ 3 * (g ^ 2)⁻¹ = g by group] at h

theorem eq_or_eq_of_relIndex_eq_three {D C N : Subgroup G} (hDC : D ≤ C) (hCN : C ≤ N)
    (h : D.relIndex N = 3) : C = D ∨ C = N := by
  have hm := Subgroup.relIndex_mul_relIndex D C N hDC hCN
  rw [h] at hm
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ (Dvd.intro _ hm)) with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hDC)
  · rw [h1] at hm
    exact Or.inr (le_antisymm hCN (Subgroup.relIndex_eq_one.mp (by omega)))

variable [Finite G]

theorem eq_one_of_mem_of_mem_center {S : Subgroup G} (hS : IsPGroup 2 S)
    (hZ : Odd (Nat.card (Subgroup.center G))) {x : G} (hxS : x ∈ S)
    (hxZ : x ∈ Subgroup.center G) : x = 1 := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hS : ∃ a, Nat.card S = 2 ^ a)
  have hSexp : ∀ s ∈ S, s ^ 2 ^ a = 1 := fun s hs => by
    have : (⟨s, hs⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [ha] at this
    simpa using congrArg Subtype.val this
  exact eq_one_of_mul_central hSexp hZ (one_mem S) hxZ (by rw [one_mul]; exact hSexp x hxS)

theorem normalizer_map_mk (hZ : Odd (Nat.card (Subgroup.center G))) {S : Subgroup G}
    (hS : IsPGroup 2 S) :
    Subgroup.normalizer ((S.map (QuotientGroup.mk' (Subgroup.center G)) : Subgroup _) :
        Set (G ⧸ Subgroup.center G)) =
      (Subgroup.normalizer (S : Set G)).map (QuotientGroup.mk' (Subgroup.center G)) := by
  set π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  have hker : π.ker = Subgroup.center G := QuotientGroup.ker_mk' _
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hS : ∃ a, Nat.card S = 2 ^ a)
  have hSexp : ∀ s ∈ S, s ^ 2 ^ a = 1 := fun s hs => by
    have : (⟨s, hs⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [ha] at this
    simpa using congrArg Subtype.val this
  refine le_antisymm ?_ (Subgroup.le_normalizer_map π)
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) xb
  have hconj : ∀ g : G, π g ∈ Subgroup.normalizer ((S.map π : Subgroup _) : Set _) →
      ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have h1 : π (g * s * g⁻¹) ∈ S.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg (π s)).mp ⟨s, hs, rfl⟩
    obtain ⟨s', hs', he⟩ := h1
    have hz : s'⁻¹ * (g * s * g⁻¹) ∈ Subgroup.center G := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hx : (s' * (s'⁻¹ * (g * s * g⁻¹))) ^ 2 ^ a = 1 := by
      rw [mul_inv_cancel_left, conj_pow, hSexp s hs, mul_one, mul_inv_cancel]
    have h1 := eq_one_of_mul_central hSexp hZ hs' hz hx
    rw [show g * s * g⁻¹ = s' * (s'⁻¹ * (g * s * g⁻¹)) by group, h1, mul_one]
    exact hs'
  refine ⟨x, ?_, rfl⟩
  show x ∈ Subgroup.normalizer (S : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact hconj x hxb s
  · intro h
    have hinv : π x⁻¹ ∈ Subgroup.normalizer ((S.map π : Subgroup _) : Set _) := by
      rw [map_inv]
      exact inv_mem hxb
    have := hconj x⁻¹ hinv _ h
    simpa [mul_assoc] using this

end Lemmas

section Reduction

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem centerDescend_mk' (α : MulAut X) (x : X) :
    centerDescend X α (QuotientGroup.mk' (Subgroup.center X) x) =
      QuotientGroup.mk' (Subgroup.center X) (α x) :=
  rfl

omit [Finite X] in
theorem map_centerDescend_eq {S : Subgroup X} {α : MulAut X} (h : S.map α.toMonoidHom = S) :
    (S.map (QuotientGroup.mk' (Subgroup.center X))).map (centerDescend X α).toMonoidHom =
      S.map (QuotientGroup.mk' (Subgroup.center X)) := by
  rw [Subgroup.map_map]
  conv_rhs => rw [← h, Subgroup.map_map]
  rfl

omit [Finite X] in
theorem pow_two_pow_centerDescend {α : MulAut X} (h : ∃ k : ℕ, α ^ 2 ^ k = 1) :
    ∃ k : ℕ, centerDescend X α ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem le_centMod_centerDescend (hZ : Odd (Nat.card (Subgroup.center X))) {S : Subgroup X}
    (hS : IsPGroup 2 S) {α : MulAut X}
    (h : ∀ b ∈ Subgroup.normalizer (S : Set X), α b * b⁻¹ ∈ S) :
    Subgroup.normalizer ((S.map (QuotientGroup.mk' (Subgroup.center X)) : Subgroup _) :
        Set (X ⧸ Subgroup.center X)) ≤
      centMod (S.map (QuotientGroup.mk' (Subgroup.center X))) (centerDescend X α) := by
  rw [normalizer_map_mk hZ hS]
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨Subgroup.le_normalizer_map _ ⟨b, hb, rfl⟩, ?_⟩
  rw [centerDescend_mk', ← map_inv, ← map_mul]
  exact ⟨_, h b hb, rfl⟩

theorem isSylowTwoOf_map_mk (hZ : Odd (Nat.card (Subgroup.center X))) {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map (QuotientGroup.mk' (Subgroup.center X))) ⊤ := by
  have h := CFSG.QuasithinUnique.Setup.X3.isSylowTwoOf_map_of_odd_ker
    (QuotientGroup.mk' (Subgroup.center X)) (by rw [QuotientGroup.ker_mk']; exact hZ) hS
  rwa [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h

theorem lieBorelInvert3_of
    (h : ∀ (M : Type) [Group M] [Finite M] (n : ℕ), 1 < n → IsSimpleGroup M →
      A315.IsLieChar2 n M → N2Model M ∧ N4Model M) : LieBorelInvert3 := by
  intro X _ _ n hn hq hZ hL S hS α hα hαS y hyN hyS hy3 hαy D hSD hDN hyD hDidx hαD
  have : Group.IsPerfect X := hq.1
  set Z := Subgroup.center X with hZdef
  set π : X →* X ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  obtain ⟨h2, h4⟩ := h (X ⧸ Z) n hn hq.2.1 hL
  set αb := centerDescend X α with hαb
  have hαbπ : ∀ x, αb (π x) = π (α x) := fun x => rfl
  have hSb := isSylowTwoOf_map_mk hZ hS
  have hN := normalizer_map_mk hZ hS.2.1
  have hαb2 := pow_two_pow_centerDescend hα
  have hαbS := map_centerDescend_eq hαS
  have hZN : Z ≤ Subgroup.normalizer (S : Set X) := Subgroup.center_le_normalizer _
  have hαSmem : ∀ s ∈ S, α s ∈ S := fun s hs => by
    have h1 : α s ∈ S.map α.toMonoidHom := ⟨s, hs, rfl⟩
    rwa [hαS] at h1
  have hDZ : (y ∈ D ⊔ Z ∨ ¬ Z ≤ D) → ∀ b ∈ Subgroup.normalizer (S : Set X), b ∈ D ⊔ Z := by
    intro hyZ b hb
    have hDE : D ≤ (D ⊔ Z) ⊓ Subgroup.normalizer (S : Set X) := le_inf le_sup_left hDN
    rcases eq_or_eq_of_relIndex_eq_three hDE inf_le_right hDidx with hE | hE
    · exfalso
      rcases hyZ with hyZ | hZD
      · exact hyD (hE ▸ (⟨hyZ, hyN⟩ : y ∈ (D ⊔ Z) ⊓ Subgroup.normalizer (S : Set X)))
      · exact hZD fun z hz => hE ▸ (⟨le_sup_right (a := D) hz, hZN hz⟩ :
          z ∈ (D ⊔ Z) ⊓ Subgroup.normalizer (S : Set X))
    · have := hE.symm ▸ hb
      exact this.1
  by_cases hyb : π y ∈ S.map π
  ·
    obtain ⟨s, hs, hsy⟩ := hyb
    obtain ⟨z, rfl⟩ : ∃ z, y = s * z := ⟨s⁻¹ * y, by group⟩
    have hπz : π z = 1 := by
      have h1 : π s = π s * π z := by rw [← map_mul]; exact hsy
      calc π z = (π s)⁻¹ * (π s * π z) := by group
        _ = 1 := by rw [← h1, inv_mul_cancel]
    have hz : z ∈ Z := by rw [← hker, MonoidHom.mem_ker]; exact hπz
    have hzc : ∀ g : X, g * z = z * g := Subgroup.mem_center_iff.mp hz
    have hz1 : z ≠ 1 := fun h1 => hyS (by rw [h1, mul_one]; exact hs)
    have hz3 : z ^ 3 = 1 := by
      have hc : Commute s z := hzc s
      have h1 : z ^ 3 = (s ^ 3)⁻¹ * (s * z) ^ 3 := by
        rw [hc.mul_pow, ← mul_assoc, inv_mul_cancel, one_mul]
      refine eq_one_of_mem_of_mem_center hS.2.1 hZ ?_ (Subgroup.pow_mem _ hz 3)
      rw [h1]
      exact mul_mem (inv_mem (pow_mem hs 3)) hy3
    have hαzZ : α z ∈ Z := mulAut_apply_mem_center α hz
    have hαz : α z = z⁻¹ := by
      have hαzc : ∀ g : X, g * α z = α z * g := Subgroup.mem_center_iff.mp hαzZ
      have h1 : α z * z = (α s * s)⁻¹ * (α (s * z) * (s * z)) := by
        rw [map_mul]
        calc α z * z = (α s * s)⁻¹ * (α s * s * (α z * z)) := by group
          _ = (α s * s)⁻¹ * (α s * α z * (s * z)) := by
            rw [mul_assoc (α s) s, ← mul_assoc s, hαzc s, mul_assoc (α z), hzc s]
            group
      have h2 : α z * z ∈ S := by
        rw [h1]
        exact mul_mem (inv_mem (mul_mem (hαSmem s hs) hs)) hαy
      have h3 := eq_one_of_mem_of_mem_center hS.2.1 hZ h2 (mul_mem hαzZ hz)
      exact eq_inv_of_mul_eq_one_left h3
    have hyDZ : s * z ∈ D ⊔ Z :=
      mul_mem (le_sup_left (a := D) (hSD hs)) (le_sup_right (a := D) hz)
    have hcent : Subgroup.normalizer ((S.map π : Subgroup _) : Set (X ⧸ Z)) ≤
        centMod (S.map π) αb := by
      rw [hN]
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨Subgroup.le_normalizer_map _ ⟨b, hb, rfl⟩, ?_⟩
      obtain ⟨d, hd, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
        (hDZ (Or.inl hyDZ) b hb)
      have hπw : π w = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hw
      have hπαw : π (α w) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact mulAut_apply_mem_center α hw
      rw [hαbπ, map_mul, map_mul, map_mul, hπw, hπαw, mul_one, mul_one, ← map_inv, ← map_mul]
      exact ⟨_, hαD d hd, rfl⟩
    rcases h4 _ hSb αb hαb2 hαbS hcent with hinn | hL34
    · exfalso
      obtain ⟨x, hx⟩ := isInnerAut_of_isInnerAut_centerDescend hinn
      have h1 : α z = z := by
        rw [← hx, MulAut.conj_apply, hzc x, mul_assoc, mul_inv_cancel, mul_one]
      rw [hαz] at h1
      apply hz1
      have h2 : z ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [← h1]; exact inv_mul_cancel z
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3, h2, inv_one, one_mul]
    · exact Or.inr (Or.inr hL34)
  ·
    have hπS : ∀ d ∈ D, π (α d) * (π d)⁻¹ ∈ S.map π := fun d hd => by
      rw [← map_inv, ← map_mul]
      exact ⟨_, hαD d hd, rfl⟩
    have hπy : π (α y) * π y ∈ S.map π := by
      rw [← map_mul]
      exact ⟨_, hαy, rfl⟩
    have hZD : Z ≤ D := by
      by_contra hZD
      obtain ⟨d, hd, w, hw, hdw⟩ := Subgroup.mem_sup_of_normal_right.mp
        (hDZ (Or.inr hZD) y hyN)
      apply hyb
      have hπw : π w = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hw
      have hπyd : π y = π d := by rw [← hdw, map_mul, hπw, mul_one]
      have hαyd : π (α y) = π (α d) := by rw [← hαbπ, hπyd, hαbπ]
      have hsq : π d ^ 2 ∈ S.map π := by
        have h1 := mul_mem (inv_mem (hπS d hd)) hπy
        rwa [hαyd, hπyd, show (π (α d) * (π d)⁻¹)⁻¹ * (π (α d) * π d) = π d ^ 2 by
          rw [pow_two]; group]
          at h1
      have hcube : π d ^ 3 ∈ S.map π := by
        rw [← hπyd, ← map_pow]
        exact ⟨_, hy3, rfl⟩
      rw [hπyd]
      exact mem_of_sq_mem_of_cube_mem hsq hcube
    have hDb : D.map π ≤ centMod (S.map π) αb := by
      rintro _ ⟨d, hd, rfl⟩
      exact ⟨Subgroup.le_normalizer_map _ ⟨d, hDN hd, rfl⟩, hαbπ d ▸ hπS d hd⟩
    have hDidx' : (D.map π).relIndex (Subgroup.normalizer ((S.map π : Subgroup _) :
        Set (X ⧸ Z))) = 3 := by
      rw [hN, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq, hker, sup_eq_left.mpr hZD]
      exact hDidx
    rcases eq_or_eq_of_relIndex_eq_three hDb (centMod_le_normalizer _ _) hDidx' with hC | hC
    · exact h2 _ hSb αb hαb2 hαbS (by rw [hC]; exact hDidx')
    · exfalso
      have hyC : π y ∈ centMod (S.map π) αb := by
        rw [hC, hN]
        exact ⟨y, hyN, rfl⟩
      apply hyb
      have hsq : π y ^ 2 ∈ S.map π := by
        have h1 := mul_mem (inv_mem hyC.2) hπy
        rwa [hαbπ, show (π (α y) * (π y)⁻¹)⁻¹ * (π (α y) * π y) = π y ^ 2 by
          rw [pow_two]; group] at h1
      have hcube : π y ^ 3 ∈ S.map π := by
        rw [← map_pow]
        exact ⟨_, hy3, rfl⟩
      exact mem_of_sq_mem_of_cube_mem hsq hcube

theorem lieBorelThreeInner_of
    (h : ∀ (M : Type) [Group M] [Finite M] (n : ℕ), 1 < n → IsSimpleGroup M →
      A315.IsLieChar2 n M → N3Model M) : LieBorelThreeInner := by
  intro X _ _ n hn hq hZ hL S hS α β hα hβ hαS hβS hinv hαc hβc
  have : Group.IsPerfect X := hq.1
  have h3 := h (X ⧸ Subgroup.center X) n hn hq.2.1 hL
  have hβ3 : centerDescend X β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hinvb : centerDescend X α * centerDescend X β * (centerDescend X α)⁻¹ =
      (centerDescend X β)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  rcases h3 _ (isSylowTwoOf_map_mk hZ hS) _ _ (pow_two_pow_centerDescend hα) hβ3
    (map_centerDescend_eq hαS) (map_centerDescend_eq hβS) hinvb
    (le_centMod_centerDescend hZ hS.2.1 hαc) (le_centMod_centerDescend hZ hS.2.1 hβc) with
    hi | hi
  · exact Or.inl (isInnerAut_of_isInnerAut_centerDescend hi)
  · exact Or.inr hi

theorem lieBorelTwoInner_of
    (h : ∀ (M : Type) [Group M] [Finite M] (n : ℕ), 1 < n → IsSimpleGroup M →
      A315.IsLieChar2 n M → N4Model M)
    (hL34 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      Odd (Nat.card (Subgroup.center X)) → IsPSL 3 2 2 (X ⧸ Subgroup.center X) →
        CFSG.pRank 3 X ≠ 1) :
    LieBorelTwoInner := by
  intro X _ _ n hn hq hZ hL hr S hS α hα hαS hαc
  have : Group.IsPerfect X := hq.1
  rcases h (X ⧸ Subgroup.center X) n hn hq.2.1 hL _ (isSylowTwoOf_map_mk hZ hS) _
    (pow_two_pow_centerDescend hα) (map_centerDescend_eq hαS)
    (le_centMod_centerDescend hZ hS.2.1 hαc) with hi | hi
  · obtain ⟨x, rfl⟩ := isInnerAut_of_isInnerAut_centerDescend hi
    obtain ⟨k, hk⟩ := hα
    have hxN : x ∈ Subgroup.normalizer (S : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        have h1 : MulAut.conj x s ∈ S.map (MulAut.conj x).toMonoidHom := ⟨s, hs, rfl⟩
        rwa [hαS] at h1
      · intro hs
        have h1 : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom := by rw [hαS]; exact hs
        obtain ⟨s', hs', he⟩ := h1
        have : s' = s := by
          have he' : x * s' * x⁻¹ = x * s * x⁻¹ := he
          simpa using he'
        rwa [← this]
    have hxZ : x ^ 2 ^ k ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut X => φ g) hk
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * x ^ 2 ^ k = x ^ 2 ^ k * g * (x ^ 2 ^ k)⁻¹ * x ^ 2 ^ k := by rw [h1]
        _ = x ^ 2 ^ k * g := by group
    set e := Nat.card (Subgroup.center X) with hedef
    set m := e ^ Nat.totient (2 ^ k) with hmdef
    have hmod : m ≡ 1 [MOD 2 ^ k] :=
      Nat.ModEq.pow_totient (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hZ))
    obtain ⟨j, hj⟩ : ((2 ^ k : ℕ) : ℤ) ∣ (m : ℤ) - 1 := Nat.modEq_iff_dvd.mp hmod.symm
    have he : (x ^ 2 ^ k) ^ e = 1 := by
      have h1 := congrArg Subtype.val
        (pow_card_eq_one' (G := Subgroup.center X) (x := ⟨x ^ 2 ^ k, hxZ⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
    have hs2 : (x ^ m) ^ 2 ^ k = 1 := by
      obtain ⟨c, hc⟩ : e ∣ m :=
        dvd_pow_self e (Nat.totient_pos.mpr (Nat.two_pow_pos k)).ne'
      rw [← pow_mul, mul_comm, pow_mul, hc, pow_mul, he, one_pow]
    have hsx : x⁻¹ * x ^ m ∈ Subgroup.center X := by
      have h1 : x⁻¹ * x ^ m = (x ^ 2 ^ k) ^ j := by
        have h2 : (-1 : ℤ) + m = ((2 ^ k : ℕ) : ℤ) * j := by linarith
        rw [← zpow_natCast x m, ← zpow_neg_one, ← zpow_add, h2, zpow_mul, zpow_natCast]
      rw [h1]
      exact Subgroup.zpow_mem _ hxZ j
    have hsS : x ^ m ∈ S := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hidx : ¬ 2 ∣ S.index := by
        have := hS.2.2
        rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
      set Q : Sylow 2 X := hS.2.1.toSylow hidx
      have hQ : (Q : Subgroup X) = S := IsPGroup.toSylow_coe hS.2.1 hidx
      have hP : IsPGroup 2 (Subgroup.zpowers (x ^ m)) := by
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hs2)
        exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
      have h1 : x ^ m ∈ Subgroup.zpowers (x ^ m) ⊓ Subgroup.normalizer (Q : Set X) := by
        refine ⟨Subgroup.mem_zpowers _, ?_⟩
        show x ^ m ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X)
        rw [hQ]
        exact pow_mem hxN m
      rw [hP.inf_normalizer_sylow Q, hQ] at h1
      exact h1.2
    refine ⟨x ^ m, hsS, MulEquiv.ext fun g => ?_⟩
    have hc := Subgroup.mem_center_iff.mp hsx
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc x * g * x⁻¹ = x * (g * (x⁻¹ * x ^ m)) * (x⁻¹ * x ^ m)⁻¹ * x⁻¹ := by group
      _ = x * ((x⁻¹ * x ^ m) * g) * (x⁻¹ * x ^ m)⁻¹ * x⁻¹ := by rw [hc g]
      _ = x ^ m * g * (x ^ m)⁻¹ := by group
  · exact absurd hr (hL34 X hq hZ hi)

end Reduction

end CFSG.Quasithin.H13.L32A.C.SkPf
