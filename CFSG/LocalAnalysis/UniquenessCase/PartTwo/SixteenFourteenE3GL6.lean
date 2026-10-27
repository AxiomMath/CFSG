module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartOne.K133H.SylowTorus
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s1614e3_card_mulAut_six {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) (hrk : rk T = 6) :
    Nat.card (MulAut T) = 20158709760 := by
  have h2 : ∀ e : T, e * e = 1 := fun e => by rw [← pow_two]; exact hT e
  have hcardT : Nat.card T = 2 ^ 6 := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hT), hrk]
  rw [CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two h2 6 hcardT]
  norm_num [Fin.prod_univ_succ]

private theorem s1614e3_mulEquiv_vec {V : Type*} [CommGroup V] [Finite V] {n : ℕ}
    (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ n) :
    Nonempty (V ≃* Multiplicative (Fin n → ZMod 2)) := by
  classical
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← sq]
    exact hV2 _
  have : Fintype (Additive V) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive V) = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    have h2 : Nat.card (Additive V) = 2 ^ n := hcard
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hfin
  let L : Additive V ≃+ (Fin n → ZMod 2) := b.equivFun.toAddEquiv
  exact ⟨{ toFun := fun v => Multiplicative.ofAdd (L (Additive.ofMul v))
           invFun := fun x => Additive.toMul (L.symm (Multiplicative.toAdd x))
           left_inv := fun v => by simp
           right_inv := fun x => by simp
           map_mul' := fun v w => by simp }⟩

private noncomputable def s1614e3_mulAutProdHom (A B : Type*) [Group A] [Group B] :
    MulAut A × MulAut B →* MulAut (A × B) where
  toFun fg := MulEquiv.prodCongr fg.1 fg.2
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

private theorem s1614e3_mulAutProdHom_apply {A B : Type*} [Group A] [Group B]
    (f : MulAut A) (g : MulAut B) (a : A) (b : B) :
    s1614e3_mulAutProdHom A B (f, g) (a, b) = (f a, g b) := rfl

private theorem s1614e3_mulAutProdHom_injective (A B : Type*) [Group A] [Group B] :
    Function.Injective (s1614e3_mulAutProdHom A B) := by
  rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ h
  have h1 : f₁ = f₂ := by
    ext a
    have := congrArg (fun e : MulAut (A × B) => (e (a, 1)).1) h
    simpa [s1614e3_mulAutProdHom_apply] using this
  have h2 : g₁ = g₂ := by
    ext b
    have := congrArg (fun e : MulAut (A × B) => (e (1, b)).2) h
    simpa [s1614e3_mulAutProdHom_apply] using this
  exact Prod.ext h1 h2

private theorem s1614e3_prodMap_injective {M N M' N' : Type*} [MulOneClass M] [MulOneClass N]
    [MulOneClass M'] [MulOneClass N'] (f : M →* M') (g : N →* N')
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (MonoidHom.prodMap f g) := by
  intro a b h
  have h1 : f a.1 = f b.1 := by
    have := congrArg Prod.fst h
    simpa using this
  have h2 : g a.2 = g b.2 := by
    have := congrArg Prod.snd h
    simpa using this
  exact Prod.ext (hf h1) (hg h2)

private theorem s1614e3_isElemAbelian_range {A G : Type*} [Group A] [Group G] {p : ℕ}
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (f : A →* G) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
    rw [← hx, ← map_pow, hpow, map_one]

theorem s1614e3_factorization_seven_le_two {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) (hrk : rk T = 6) (H : Subgroup (MulAut T)) :
    (Nat.card H).factorization 7 ≤ 2 := by
  have hmul := s1614e3_card_mulAut_six hT hrk
  have hdvd : Nat.card H ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card H
  rw [hmul] at hdvd
  by_contra h
  have h3 : 3 ≤ (Nat.card H).factorization 7 := by omega
  have hdvd7 : 7 ^ 3 ∣ Nat.card H :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_seven
      (Nat.card_pos (α := H)).ne').2 h3
  have : 7 ^ 3 ∣ 20158709760 := hdvd7.trans hdvd
  norm_num at this

theorem s1614e3_pRank_seven_le_two {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (hrk : rk T = 6) (H : Subgroup (MulAut T)) : CFSG.Open.pRank 7 H ≤ 2 := by
  have hmul := s1614e3_card_mulAut_six hT hrk
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 7) ?_
  intro E hEH hE
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hE7 : IsPGroup 7 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 (x : MulAut T) x.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 7)).mp hE7
  have hdvd : 7 ^ n ∣ 20158709760 := by
    rw [← hn]
    exact (Subgroup.card_dvd_of_le hEH).trans
      (by rw [← hmul]; exact Subgroup.card_subgroup_dvd_card H)
  have hnle : n ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ n := by omega
    have hdvd3 : 7 ^ 3 ∣ 20158709760 := (pow_dvd_pow 7 h3).trans hdvd
    norm_num at hdvd3
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) hnle

theorem s1614e3_factorization_three_le {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) (hrk : rk T = 6) (H : Subgroup (MulAut T)) :
    (Nat.card H).factorization 3 ≤ 4 := by
  have hmul := s1614e3_card_mulAut_six hT hrk
  have hdvd : Nat.card H ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card H
  rw [hmul] at hdvd
  by_contra h
  have h5 : 5 ≤ (Nat.card H).factorization 3 := by omega
  have hdvd3 : 3 ^ 5 ∣ Nat.card H :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos (α := H)).ne').2 h5
  have : 3 ^ 5 ∣ 20158709760 := hdvd3.trans hdvd
  norm_num at this

theorem s1614e3_exists_E27 {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (hrk : rk T = 6) : ∃ E : Subgroup (MulAut T), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let V := Multiplicative (Fin 2 → ZMod 2)
  have hV2 : ∀ v : V, v * v = 1 := by decide
  have hVcard : Nat.card V = 2 ^ 2 := by
    simp [V, Nat.card_fun, ZMod.card]
  have hV6 : Nat.card (MulAut V) = 6 :=
    (CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hV2 2 hVcard).trans
      (by norm_num [Fin.prod_univ_succ])
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hV6]; norm_num)
  let K : Subgroup (MulAut V) := Subgroup.zpowers c
  have hK : Nat.card K = 3 := by rw [Nat.card_zpowers, hc]
  have hTcard : Nat.card T = 2 ^ 6 := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hT), hrk]
  obtain ⟨e1⟩ := s1614e3_mulEquiv_vec (n := 6) hT hTcard
  have hV3pow : ∀ x : V × (V × V), x * x = 1 := by
    intro x
    refine Prod.ext ?_ ?_
    · change x.1 * x.1 = 1; exact hV2 x.1
    · refine Prod.ext ?_ ?_
      · change x.2.1 * x.2.1 = 1; exact hV2 x.2.1
      · change x.2.2 * x.2.2 = 1; exact hV2 x.2.2
  have hV3card : Nat.card (V × (V × V)) = 2 ^ 6 := by
    rw [Nat.card_prod, Nat.card_prod, hVcard]; norm_num
  obtain ⟨e2⟩ := s1614e3_mulEquiv_vec (n := 6)
    (fun x => (pow_two x).trans (hV3pow x)) hV3card
  let eT : T ≃* (V × (V × V)) := e1.trans e2.symm
  let A := K × (K × K)
  have hAcard : Nat.card A = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, hK]; norm_num
  have hAcomm : ∀ a b : A, a * b = b * a := fun a b => mul_comm' a b
  have hK3 : ∀ x : K, x ^ 3 = 1 := fun x => by
    have h := pow_card_eq_one' (x := x)
    rwa [hK] at h
  have hApow : ∀ a : A, a ^ 3 = 1 := by
    intro a
    refine Prod.ext ?_ ?_
    · change a.1 ^ 3 = 1; exact hK3 a.1
    · refine Prod.ext ?_ ?_
      · change a.2.1 ^ 3 = 1; exact hK3 a.2.1
      · change a.2.2 ^ 3 = 1; exact hK3 a.2.2
  let g : A →* (MulAut V × (MulAut V × MulAut V)) :=
    MonoidHom.prodMap K.subtype (MonoidHom.prodMap K.subtype K.subtype)
  have hg : Function.Injective g :=
    s1614e3_prodMap_injective K.subtype (MonoidHom.prodMap K.subtype K.subtype)
      Subtype.val_injective (s1614e3_prodMap_injective K.subtype K.subtype
        Subtype.val_injective Subtype.val_injective)
  let θ : MulAut V × (MulAut V × MulAut V) →* MulAut (V × (V × V)) :=
    (s1614e3_mulAutProdHom V (V × V)).comp
      (MonoidHom.prodMap (MonoidHom.id (MulAut V)) (s1614e3_mulAutProdHom V V))
  have hθ : Function.Injective θ :=
    (s1614e3_mulAutProdHom_injective V (V × V)).comp
      (s1614e3_prodMap_injective (MonoidHom.id (MulAut V)) (s1614e3_mulAutProdHom V V)
        Function.injective_id (s1614e3_mulAutProdHom_injective V V))
  let f : A →* MulAut T := (MulAut.congr eT.symm).toMonoidHom.comp (θ.comp g)
  have hf : Function.Injective f :=
    (MulAut.congr eT.symm).injective.comp (hθ.comp hg)
  refine ⟨f.range, s1614e3_isElemAbelian_range hAcomm hApow f, ?_⟩
  have hcardrange : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  rw [hcardrange, hAcard]

theorem s1614e3_three_le_pRank_of_card {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) (hrk : rk T = 6) (H : Subgroup (MulAut T))
    (h81 : (Nat.card H).factorization 3 = 4) : 3 ≤ CFSG.Open.pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hE, hEcard⟩ := s1614e3_exists_E27 hT hrk
  have hle1 : (Nat.card H).factorization 3 ≤
      (Nat.card (⊤ : Subgroup (MulAut T))).factorization 3 := by
    have hdvd : Nat.card H ∣ Nat.card (⊤ : Subgroup (MulAut T)) := by
      rw [Subgroup.card_top]
      exact Subgroup.card_subgroup_dvd_card H
    exact (Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr hdvd 3
  have hle2 : (Nat.card (⊤ : Subgroup (MulAut T))).factorization 3 ≤ 4 :=
    s1614e3_factorization_three_le hT hrk (⊤ : Subgroup (MulAut T))
  have htop : (Nat.card (⊤ : Subgroup (MulAut T))).factorization 3 = 4 := by
    have h4 : 4 ≤ (Nat.card (⊤ : Subgroup (MulAut T))).factorization 3 := by
      rw [← h81]; exact hle1
    omega
  have hord : (Nat.card (⊤ : Subgroup (MulAut T))).factorization 3 =
      (Nat.card H).factorization 3 := by rw [htop, h81]
  obtain ⟨g, -, hgE⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow
    (Y := ⊤) (H := H) (A := E) le_top le_top hE.2 hord
  have hE' : IsElemAbelian 3 (E.map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj g).toMonoidHom
  have hcard' : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hgE hE' hcard'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
