module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.AlgebraicGroups

theorem centralizer_le_comap_conj_of_toralCentralizer_eq
    {τ : Tag} {L : Type} [Field L]
    {C : Type*} [Group C] (ι : C →* ModGL τ L) (F : L →+* L) {n g : ModGL τ L}
    (hgG : g ∈ adjointGroup τ L) (hFg : Units.map (entrywiseHom F) g = g * n)
    (hrange : ι.range = adjointGroup τ L ⊓ (Units.map (entrywiseHom F)).eqLocus
      (MonoidHom.id _))
    {T₀ : Subgroup (ModGL τ L)}
    (hchar : ∀ u ∈ torusGroup τ L, (n * Units.map (entrywiseHom F) u * n⁻¹ = u ↔ u ∈ T₀))
    {t : C} {c : Fin τ.rank → Lˣ} (hct : g * rootDiagUnit τ c * g⁻¹ = ι t)
    (hX : toralCentralizer τ L c = torusGroup τ L) :
    Subgroup.centralizer {t} ≤ (T₀.map (MulAut.conj g).toMonoidHom).comap ι := by
  intro y hy
  have hyt : t * y = y * t := Subgroup.mem_centralizer_iff.1 hy t rfl
  have hyF : ι y ∈ ι.range := ⟨y, rfl⟩
  rw [hrange] at hyF
  obtain ⟨hyG, hyFix⟩ := Subgroup.mem_inf.1 hyF
  have hyFix' : Units.map (entrywiseHom F) (ι y) = ι y := hyFix
  obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * ι y * g := ⟨_, rfl⟩
  have huG : u ∈ adjointGroup τ L := hu ▸ mul_mem (mul_mem (inv_mem hgG) hyG) hgG
  have hdc : rootDiagUnit τ c = g⁻¹ * ι t * g := by
    rw [← hct]
    group
  have huc : u ∈ Subgroup.centralizer {rootDiagUnit τ c} := by
    rw [Subgroup.mem_centralizer_singleton_iff, hdc, hu]
    have hιyt : ι t * ι y = ι y * ι t := by rw [← map_mul, hyt, map_mul]
    calc g⁻¹ * ι y * g * (g⁻¹ * ι t * g) = g⁻¹ * (ι y * ι t) * g := by group
      _ = g⁻¹ * (ι t * ι y) * g := by rw [hιyt]
      _ = g⁻¹ * ι t * g * (g⁻¹ * ι y * g) := by group
  have huH : u ∈ torusGroup τ L := by
    rw [← hX]
    exact Subgroup.mem_inf.2 ⟨huG, huc⟩
  have h2 : g * u * g⁻¹ = ι y := by
    rw [hu]
    group
  have hufix : n * Units.map (entrywiseHom F) u * n⁻¹ = u := by
    have h1 : Units.map (entrywiseHom F) (g * u * g⁻¹) =
        g * (n * Units.map (entrywiseHom F) u * n⁻¹) * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFg]
      group
    rw [h2, hyFix', ← h2] at h1
    simpa using h1.symm
  exact ⟨u, (hchar u huH).1 hufix, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h2⟩

theorem F4_cyclic_torus_core
    (K : Type) [Field K] [Finite K] {w : WeylGroup .F4}
    (D : F4CyclicBasis w)
    (horb : ∀ α, IsRoot .F4 α → ∃ k : ℕ,
      |(CFSG.RankThree.Lattice.orbitMat (weylMatrix w) α Tag.F4.rank).det| = 2 ^ k)
    (d : ℕ) (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 4 - D.ε * (Nat.card K : ℤ) ^ 2 + 1) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) :
    ∃ T : Subgroup (adjointGroup .F4 K), IsCyclic T ∧ Nat.card T = d ∧
      ∀ t ∈ T, orderOf t = p → Subgroup.centralizer {t} = T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : ExpChar L (ringChar K) := ExpChar.prime hℓ
  set F : L →+* L := iterateFrobenius L (ringChar K) e
  have hF : ∀ c : L, F c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hq, Nat.card_eq_fintype_card, hqe]
  have hFbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) L (e : ℕ) e.pos).1 .F4
  obtain ⟨n, hn, hnG⟩ : ∃ n, n = canonicalRep (coxeterSystem .F4) L w ∧
      n ∈ adjointGroup .F4 L := ⟨_, rfl, canonicalRep_mem_adjointGroup _ L w⟩
  obtain ⟨g₀, hg₀⟩ := hLang ⟨n, hnG⟩
  set g : ModGL .F4 L := (g₀ : ModGL .F4 L) with hgdef
  have hFg : Units.map (entrywiseHom F) g = g * n := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS] at h
    rw [h, mul_inv_cancel_left]
  have hgG : g ∈ adjointGroup .F4 L := g₀.2
  set T₀ := D.torus L q d with hT₀
  have hT₀H : T₀ ≤ torusGroup .F4 L := D.torus_le_torusGroup q d
  have hHG : torusGroup .F4 L ≤ adjointGroup .F4 L := torusGroup_le_adjointGroup_F4
  have hHcomm := (triangular_borel_structure.{0, 0} .F4 L).1
  have hchar : ∀ u ∈ torusGroup .F4 L,
      (n * Units.map (entrywiseHom F) u * n⁻¹ = u ↔ u ∈ T₀) := fun u hu => by
    rw [hn]
    exact D.conj_frob_eq_iff_mem_torus F hF hd hu
  have hqK : ((q : ℕ) : K) = 0 := by
    rw [hq, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have hdK : (d : K) = 1 := by
    have h := congrArg (Int.cast : ℤ → K) hd
    push_cast at h
    rw [h, hqK]
    ring
  have : NeZero (d : L) := ⟨by
    rw [← map_natCast (algebraMap K L), hdK, map_one]
    exact one_ne_zero⟩
  have : NeZero d := ⟨fun h0 => by simp [h0] at hdK⟩
  have hcardT₀ : Nat.card T₀ = d := D.natCard_torus q d
  have hcycT₀ : IsCyclic T₀ := D.isCyclic_torus q d
  set Tc := T₀.map (MulAut.conj g).toMonoidHom with hTc
  obtain ⟨ι, hι⟩ : ∃ ι : adjointGroup .F4 K →* ModGL .F4 L,
      ι = (baseChangeGL (algebraMap K L)).comp (adjointGroup .F4 K).subtype := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact (baseChangeGL_injective (τ := .F4) (algebraMap K L)).comp Subtype.val_injective
  have hrange : ι.range = adjointGroup .F4 L ⊓ (Units.map (entrywiseHom F)).eqLocus
      (MonoidHom.id _) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype,
      frobenius_fixed_eq_map_of_bijective (Or.inr rfl) F hF hFbij]
  have hconjF : ∀ u : ModGL .F4 L, Units.map (entrywiseHom F) (g * u * g⁻¹) =
      g * (n * Units.map (entrywiseHom F) u * n⁻¹) * g⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hFg]
    group
  have hTcι : Tc ≤ ι.range := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG (hHG (hT₀H hu))) (inv_mem hgG), ?_⟩
    change Units.map (entrywiseHom F) (g * u * g⁻¹) = g * u * g⁻¹
    rw [hconjF, (hchar u (hT₀H hu)).2 hu]
  set T := Tc.comap ι with hT
  have eT : T ≃* T₀ :=
    ((Subgroup.equivMapOfInjective T ι hιinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTcι))).trans
      (Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  have hcardT : Nat.card T = d := by rw [Nat.card_congr eT.toEquiv, hcardT₀]
  have hcycT : IsCyclic T := isCyclic_of_injective eT.toMonoidHom eT.injective
  have hTcomm : ∀ y ∈ T, ∀ z ∈ T, y * z = z * y := by
    intro y hy z hz
    apply hιinj
    obtain ⟨u, hu, hyu⟩ := hy
    obtain ⟨u', hu', hzu⟩ := hz
    rw [map_mul, map_mul, ← hyu, ← hzu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := hHcomm u (hT₀H hu) u' (hT₀H hu')
    calc g * u * g⁻¹ * (g * u' * g⁻¹) = g * (u * u') * g⁻¹ := by group
      _ = g * (u' * u) * g⁻¹ := by rw [hc]
      _ = g * u' * g⁻¹ * (g * u * g⁻¹) := by group
  refine ⟨T, hcycT, hcardT, fun t ht hto => ?_⟩
  have ht' := ht
  obtain ⟨h, hh, hht⟩ := ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hT₀H hh)
  have hoc' : orderOf (rootDiagUnit .F4 c) = p := by
    rw [← orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
        (rootDiagUnit .F4 c), hht, orderOf_injective ι hιinj t, hto]
  have hoc : orderOf c = p := (orderOf_rootDiagUnit c).symm.trans hoc'
  have hcp : c ^ p = 1 := hoc ▸ pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hoc
    exact hp.one_lt.ne hoc
  have hfix : ∀ v, rootChar c (w • v) = rootChar c v ^ q :=
    (conj_frob_rootDiagUnit_eq_iff F hF w c).1 (hn ▸ (hchar _ (hT₀H hh)).2 hh)
  have hX : toralCentralizer .F4 L c = torusGroup .F4 L :=
    F4_centralizer_eq_torusGroup_of_regular hp hp3 hoc' fun α hα =>
      rootChar_ne_one_of_forall_smul_eq_pow hp (by omega) horb hfix hcp hc1 hα
  refine le_antisymm
    (centralizer_le_comap_conj_of_toralCentralizer_eq ι F hgG hFg hrange hchar hht hX)
    fun y hy => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hTcomm z ht' y hy

theorem natCast_zmod_ne_zero_of_pos_of_lt {p a : ℕ} (ha0 : 0 < a) (hap : a < p) :
    ((a : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)

theorem F4_not_dvd_index_of_card_eq
    (K : Type) [Field K] [Finite K] {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (d : ℕ)
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 4 - ε * (Nat.card K : ℤ) ^ 2 + 1) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d) (T : Subgroup (adjointGroup .F4 K))
    (hT : Nat.card T = d) : ¬ p ∣ T.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := T.card_mul_index
  rw [hT, card_adjointGroup_F4, CFSG.Open.ordF4] at hcard
  set Q : ℤ := (Nat.card K : ℤ) with hQ
  have hcardZ : (d : ℤ) * T.index =
      Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at h
    exact h
  have hd0 : (d : ℤ) ≠ 0 := by
    rw [← hT]
    exact_mod_cast Nat.card_pos.ne'
  have two : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) (by omega : 2 < p)
  have three : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) hp3
  set x : ZMod p := ((Nat.card K : ℕ) : ZMod p) with hx
  have hQx : ((Q : ℤ) : ZMod p) = x := by rw [hQ, Int.cast_natCast]
  have hxd : x ^ 4 - (ε : ZMod p) * x ^ 2 + 1 = 0 := by
    have h := congrArg (Int.cast : ℤ → ZMod p) hd
    push_cast at h
    rw [hQx] at h
    rw [← h]
    exact (ZMod.natCast_eq_zero_iff d p).2 hpd
  intro hdvd
  have hi : ((T.index : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
  rcases hε with rfl | rfl
  · have hidx : (T.index : ℤ) =
        Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
      apply mul_left_cancel₀ hd0
      rw [hcardZ, hd]
      ring
    have h0 := congrArg (Int.cast : ℤ → ZMod p) hidx
    push_cast at h0 hxd
    rw [hQx, hi] at h0
    have hf : x ^ 4 + 1 = 0 := by linear_combination hxd
    refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) h0.symm
    · refine pow_ne_zero _ fun h => one_ne_zero (?_ : (1 : ZMod p) = 0)
      linear_combination hf - x ^ 3 * h
    · exact fun h => two (by linear_combination (x ^ 8 - x ^ 4 + 1) * hf - h)
    · exact fun h => two (by linear_combination hf - h)
    · exact fun h => two (by linear_combination (x ^ 2 + 1 - x ^ 4) * hf + (x ^ 2 - 1) * h)
    · exact fun h => two (by linear_combination hf - (x ^ 2 + 1) * h)
  · have hidx : (T.index : ℤ) =
        Q ^ 24 * (Q ^ 6 - 1) * (Q ^ 2 + 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
      apply mul_left_cancel₀ hd0
      rw [hcardZ, hd]
      ring
    have h0 := congrArg (Int.cast : ℤ → ZMod p) hidx
    push_cast at h0 hxd
    rw [hQx, hi] at h0
    have hf : x ^ 4 - x ^ 2 + 1 = 0 := by linear_combination hxd
    refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_)
      ?_) h0.symm
    · refine pow_ne_zero _ fun h => one_ne_zero (?_ : (1 : ZMod p) = 0)
      linear_combination hf + (x - x ^ 3) * h
    · exact fun h => two (by linear_combination (x ^ 2 + 1) * hf - h)
    · exact fun h => three (by linear_combination hf + (2 - x ^ 2) * h)
    · exact fun h => three (by
        linear_combination (x ^ 4 + 2 * x ^ 2 + 1 - x ^ 6) * hf + (x ^ 2 - 2) * h)
    · exact fun h => two (by linear_combination (x ^ 2 + 1) * hf - h)
    · exact fun h => one_ne_zero (by linear_combination hf - x ^ 2 * h : (1 : ZMod p) = 0)

theorem odd_pow_four_sub_sq_add_one (q : ℕ) : Odd (q ^ 4 - q ^ 2 + 1) := by
  have h : q ^ 4 - q ^ 2 = q ^ 2 * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_one, ← pow_add]
  rw [h]
  exact (Nat.even_mul_pred_self (q ^ 2)).add_one

theorem odd_pow_four_add_one_of_even {q : ℕ} (hq : Even q) : Odd (q ^ 4 + 1) :=
  (hq.pow_of_ne_zero (by norm_num)).add_one

theorem exists_odd_of_pow_four_add_one {q : ℕ} (hq : Odd q) :
    ∃ d' : ℕ, Odd d' ∧ q ^ 4 + 1 = 2 * d' := by
  obtain ⟨k, rfl⟩ := hq
  exact ⟨8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 + 4 * k + 1,
    ⟨4 * k ^ 4 + 8 * k ^ 3 + 6 * k ^ 2 + 2 * k, by ring⟩, by ring⟩

theorem natCard_sylow_two_of_odd {G : Type*} [Group G] [Finite G] (hG : Odd (Nat.card G))
    (S : Sylow 2 G) : Nat.card S = 1 := by
  rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd
    (fun h => (Nat.not_even_iff_odd.2 hG) (even_iff_two_dvd.2 h)), pow_zero]

theorem natCard_sylow_two_of_eq_two_mul_odd {G : Type*} [Group G] [Finite G] {d' : ℕ}
    (hd' : Odd d') (hG : Nat.card G = 2 * d') (S : Sylow 2 G) : Nat.card S = 2 := by
  have hd0 : d' ≠ 0 := fun h => by simp [h] at hd'
  rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul (by norm_num) hd0,
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.2 hd') (even_iff_two_dvd.2 h)), add_zero, pow_one]

theorem F4_cyclotomic_eight_twelve_tori_and_prime_centralizers
    (K : Type) [Field K] [Finite K]
    (m d : ℕ)
    (hd : (m = 8 ∧ d = Nat.card K ^ 4 + 1) ∨ (m = 12 ∧ d = Nat.card K ^ 4 - Nat.card K ^ 2 + 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d) :
    ∃ T : Subgroup (adjointGroup .F4 K), IsCyclic T ∧ Nat.card T = d ∧
      (∃ S : Sylow p (adjointGroup .F4 K), (S : Subgroup (adjointGroup .F4 K)) ≤ T) ∧
      (∀ P : Subgroup (adjointGroup .F4 K), IsPGroup p P → IsCyclic P) ∧
      (∀ x : adjointGroup .F4 K, orderOf x = p →
        (∃ g : adjointGroup .F4 K, g * x * g⁻¹ ∈ T) ∧
        ∃ g : adjointGroup .F4 K,
          (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom = T) ∧
      (∀ S : Sylow 2 T, Nat.card S ≤ 2) ∧
      (¬ (m = 8 ∧ Odd (Nat.card K)) → Odd (Nat.card T)) ∧
      (m = 8 → Odd (Nat.card K) → ∀ S : Sylow 2 T, Nat.card S = 2) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K (RootModule .F4 K)) := Module.finite_of_finite K
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨T, hcyc, hcard, hcent, hidx⟩ : ∃ T : Subgroup (adjointGroup .F4 K), IsCyclic T ∧
      Nat.card T = d ∧ (∀ t ∈ T, orderOf t = p → Subgroup.centralizer {t} = T) ∧
      ¬ p ∣ T.index := by
    rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · have hdZ : ((Nat.card K ^ 4 + 1 : ℕ) : ℤ) =
          (Nat.card K : ℤ) ^ 4 - f4W8CyclicBasis.ε * (Nat.card K : ℤ) ^ 2 + 1 := by
        change _ = _ - (0 : ℤ) * _ + 1
        push_cast
        ring
      obtain ⟨T, h1, h2, h3⟩ := F4_cyclic_torus_core K f4W8CyclicBasis
        (fun α hα => orbit_det_f4W8Elt hα) _ hdZ hp hp3
      exact ⟨T, h1, h2, h3, F4_not_dvd_index_of_card_eq K (Or.inl rfl) _ hdZ hp hp3 hpd T h2⟩
    · have hle : Nat.card K ^ 2 ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
      have hdZ : ((Nat.card K ^ 4 - Nat.card K ^ 2 + 1 : ℕ) : ℤ) =
          (Nat.card K : ℤ) ^ 4 - f4W12CyclicBasis.ε * (Nat.card K : ℤ) ^ 2 + 1 := by
        change _ = _ - (1 : ℤ) * _ + 1
        push_cast [Nat.cast_sub hle]
        ring
      obtain ⟨T, h1, h2, h3⟩ := F4_cyclic_torus_core K f4W12CyclicBasis
        (fun α hα => orbit_det_f4Coxeter hα) _ hdZ hp hp3
      exact ⟨T, h1, h2, h3, F4_not_dvd_index_of_card_eq K (Or.inr rfl) _ hdZ hp hp3 hpd T h2⟩
  have hconjT : ∀ P : Subgroup (adjointGroup .F4 K), IsPGroup p P →
      ∃ g : adjointGroup .F4 K, P.map (MulAut.conj g).toMonoidHom ≤ T := fun P hP =>
    exists_conj_map_le_of_not_dvd_index hidx hP
  have htwo : (¬ (m = 8 ∧ Odd (Nat.card K)) → Odd (Nat.card T)) ∧
      (m = 8 → Odd (Nat.card K) → ∀ S : Sylow 2 T, Nat.card S = 2) := by
    rw [hcard]
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨fun h => ?_, fun _ hq S => ?_⟩
      · have hq : Even (Nat.card K) := by
          rcases Nat.even_or_odd (Nat.card K) with h' | h'
          · exact h'
          · exact absurd ⟨rfl, h'⟩ h
        exact odd_pow_four_add_one_of_even hq
      · obtain ⟨d', hd', hd'eq⟩ := exists_odd_of_pow_four_add_one hq
        exact natCard_sylow_two_of_eq_two_mul_odd hd' (hcard.trans hd'eq) S
    · exact ⟨fun _ => odd_pow_four_sub_sq_add_one _, fun h => absurd h (by norm_num)⟩
  refine ⟨T, hcyc, hcard, ?_, fun P hP => ?_, fun x hx => ?_, fun S => ?_, htwo⟩
  · obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
    have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
    have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
      rw [Subgroup.index_map_subtype]
      exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hidx
    exact ⟨hS.toSylow hSi, by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _⟩
  · obtain ⟨g, hg⟩ := hconjT P hP
    exact isCyclic_of_injective
      (MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp P.subtype) T
        fun y => hg ⟨y, y.2, rfl⟩)
      fun y z h => Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  · have hPx : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨g, hg⟩ := hconjT _ hPx
    have hxT : g * x * g⁻¹ ∈ T := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hto : orderOf (g * x * g⁻¹) = p := by
      rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
        orderOf_injective _ (MulAut.conj g).injective x, hx]
    exact ⟨⟨g, hxT⟩, g, by rw [map_conj_centralizer_singleton_eq, hcent _ hxT hto]⟩
  · by_cases h8 : m = 8 ∧ Odd (Nat.card K)
    · rw [htwo.2 h8.1 h8.2 S]
    · rw [natCard_sylow_two_of_odd (htwo.1 h8) S]
      norm_num

end CFSG.RankThree.Chevalley
