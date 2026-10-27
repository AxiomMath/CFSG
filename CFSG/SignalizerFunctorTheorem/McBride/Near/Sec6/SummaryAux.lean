module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Final
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515e.Basic

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S34

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

structure DistE (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E : Subgroup G) : Prop where
  mem : E ∈ signalizerFunctorEk p 1 A
  not_mem : E ∉ rSetN p A θ 1

structure Data (h : Counterexample p A θ) (E : Subgroup G) (f : G) : Prop where
  distE : DistE p A θ E
  mem : f ∈ A
  not_mem : f ∉ E

theorem DistE.of_isSolvable
    (h : Counterexample p A θ) {E : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hEs : Group.IsSolvable (thetaOf θ E)) :
    DistE p A θ E := by
  refine ⟨hE, fun hR => ?_⟩
  obtain ⟨-, -, hns, -⟩ := h.mem_rSetN_iff.mp hR
  exact hns hEs

theorem DistE.eq
    (h : Counterexample p A θ) {E E' : Subgroup G} (hE : DistE p A θ E)
    (hE' : DistE p A θ E') : E = E' := by
  obtain ⟨E₀, -, hu⟩ := h.thm617a
  exact (hu E ⟨hE.mem, hE.not_mem⟩).trans (hu E' ⟨hE'.mem, hE'.not_mem⟩).symm

theorem DistE.isSolvable
    (h : Counterexample p A θ) {E : Subgroup G} (hE : DistE p A θ E) :
    Group.IsSolvable (thetaOf θ E) := by
  by_contra hns
  refine hE.not_mem (h.mem_rSetN_iff.mpr ⟨?_, hE.mem.1, hns, by simpa using hE.mem.2⟩)
  rintro rfl
  have := hE.mem.2
  rw [Subgroup.card_bot, pow_one] at this
  exact h.hyp.prime.one_lt.ne this

omit [Finite G] in
theorem map_conj_map_conj (J : Subgroup G) (a b : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

section Apply

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.ne_one (d : Data h E f) : f ≠ 1 := fun h1 => d.not_mem (h1 ▸ one_mem E)

theorem Data.not_isSolvable
    (d : Data h E f) : ¬ Group.IsSolvable (θ f) := by
  intro hs
  have hθ := h.hyp.nearFunctor
  have hz : DistE p A θ (Subgroup.zpowers f) :=
    ⟨zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian d.mem d.ne_one, fun hR =>
      (h.zpowers_mem_rSetN_one_iff.mp hR).2.2 hs⟩
  exact d.not_mem ((d.distE.eq h hz) ▸ Subgroup.mem_zpowers f)

theorem Data.zpowers_mem_rSetN_one
    (d : Data h E f) : Subgroup.zpowers f ∈ rSetN p A θ 1 :=
  h.zpowers_mem_rSetN_one_iff.mpr ⟨d.mem, d.ne_one, d.not_isSolvable⟩

theorem Data.zpowers_mem_rSet
    (d : Data h E f) : Subgroup.zpowers f ∈ rSet p A θ :=
  d.zpowers_mem_rSetN_one.1

theorem Data.sol_eq_bot
    (d : Data h E f) : sol (θ f) = ⊥ := by
  have := Sec6S31.sol_thetaOf_eq_bot h d.zpowers_mem_rSet
  rwa [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one] at this

theorem Data.mtil (d : Data h E f) : θ f ∈ mtil p A θ :=
  Near.apply_mem_mtil h.hyp.nearFunctor d.mem d.ne_one

theorem Data.lcal_kOf
    (d : Data h E f) : lcal (kOf (θ f)) = lcal (θ f) := by
  rw [(isSemisimple_kOf d.sol_eq_bot).lcal_eq, simpleComponents_kOf d.sol_eq_bot]

theorem Data.isDirectProduct
    (d : Data h E f) : IsDirectProduct (lcal (θ f)) (kOf (θ f)) :=
  isDirectProduct_lcal_kOf d.sol_eq_bot

theorem Data.lcal_nonempty
    (d : Data h E f) : (lcal (θ f)).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hK := d.isDirectProduct.sSup_eq
  rw [hne, sSup_empty] at hK
  exact Counterexample.kOf_ne_bot_of_not_isSolvable d.not_isSolvable hK.symm

theorem Data.eq_khat
    (d : Data h E f) : θ f = khat (θ f) := by
  have hz := d.zpowers_mem_rSet
  have hthe := h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one
  have hK : perfRes (θ f) = kOf (θ f) := by
    have := h.perfRes_thetaOf_eq_kOf (B := Subgroup.zpowers f)
      (fun hb => d.ne_one (Subgroup.zpowers_eq_bot.mp hb)) (Subgroup.zpowers_le.mpr d.mem)
      (by rw [hthe]; exact d.not_isSolvable)
    rwa [hthe] at this
  have h614 := h.lemma614 hz
  rw [hthe] at h614
  refine le_antisymm ?_ (khat_le _)
  calc θ f = thetaStarFun p A θ f := (h.thetaStarFun_eq d.mem d.ne_one).symm
    _ = perfRes (θ f) ⊔ (θ f ⊓ sTwo p A θ) := rfl
    _ ≤ khat (θ f) := by
      rw [hK]
      exact sup_le (Nonsolv.kOf_le_khat_of_sol_eq_bot d.sol_eq_bot) h614.2

theorem Data.mem_normalizer_of_mem
    {x : G} (d : Data h E f) (hx : x ∈ θ f) {L : Subgroup G}
    (hL : L ∈ lcal (θ f)) : x ∈ Subgroup.normalizer (L : Set G) := by
  have hk : x ∈ khat (θ f) := d.eq_khat ▸ hx
  exact ((Nonsolv.T515e.mem_khat_iff_of_sol_eq_bot d.sol_eq_bot).mp hk).2 L hL

theorem Data.mem_sup_iff
    (d : Data h E f) {a : G} (ha : a ∈ A) :
    a ∈ E ⊔ Subgroup.zpowers f ↔ ∀ L ∈ lcal (θ f), a ∈ Subgroup.normalizer (L : Set G) := by
  have hθ := h.hyp.nearFunctor
  have h617 := h.thm617b d.distE.mem d.distE.not_mem d.mem d.not_mem
  have hAH : A ≤ Subgroup.normalizer (θ f : Set G) := hθ.isFunctor.normalized f d.mem d.ne_one
  have key := Nonsolv.L69.mem_khat_sup_iff hθ.elemAbelian.1 hAH d.sol_eq_bot d.lcal_nonempty
    (Subgroup.mem_sup_right ha : a ∈ θ f ⊔ A)
  rw [h617, Subgroup.mem_inf, sup_comm A (θ f)]
  exact ⟨fun hh => key.mp hh.2, fun hh => ⟨ha, key.mpr hh⟩⟩

theorem Data.sup_le (d : Data h E f) : E ⊔ Subgroup.zpowers f ≤ A :=
  _root_.sup_le d.distE.mem.1 (Subgroup.zpowers_le.mpr d.mem)

end Apply

omit [Finite G] in
theorem card_sup_of_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, Commute x y)
    (hd : H ⊓ K = ⊥) : Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let φ : H × K → (H ⊔ K : Subgroup G) := fun xy =>
    ⟨(xy.1 : G) * xy.2, mul_mem (Subgroup.mem_sup_left xy.1.2) (Subgroup.mem_sup_right xy.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    have h1 : (x : G) * y = x' * y' := congrArg Subtype.val hxy
    have h2 : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
      have : (x' : G)⁻¹ * (x * y) = y' := by rw [h1]; group
      calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
        _ = y' * (y : G)⁻¹ := by rw [this]
    have hmem : (x' : G)⁻¹ * x ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem x'.2) x.2, h2 ▸ K.mul_mem y'.2 (K.inv_mem y.2)⟩
    rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hx : x = x' := Subtype.ext hmem.symm
    subst hx
    have : (y : G) = y' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_commute hc).mp hz
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

section Orbit

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.card_zpowers (d : Data h E f) : Nat.card (Subgroup.zpowers f) = p := by
  have hθ := h.hyp.nearFunctor
  rw [(zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian d.mem d.ne_one).2, pow_one]

theorem Data.card_sup (d : Data h E f) :
    Nat.card (E ⊔ Subgroup.zpowers f : Subgroup G) = p ^ 2 := by
  have hθ := h.hyp.nearFunctor
  have hcE : Nat.card E = p := by rw [d.distE.mem.2, pow_one]
  have hnle : ¬ Subgroup.zpowers f ≤ E := fun hle => d.not_mem (hle (Subgroup.mem_zpowers f))
  have hd := inf_eq_bot_of_not_le hθ.prime d.card_zpowers hnle
  rw [card_sup_of_commute (fun x hx y hy => comm_of_mem_of_isMulCommutative hθ.elemAbelian.1
    (d.distE.mem.1 hx) (Subgroup.zpowers_le.mpr d.mem hy)) hd, hcE, d.card_zpowers, sq]

theorem Data.exists_mem_sdiff (d : Data h E f) : ∃ e ∈ A, e ∉ E ⊔ Subgroup.zpowers f := by
  by_contra hcon
  push Not at hcon
  have hle : A ≤ E ⊔ Subgroup.zpowers f := fun a ha => hcon a ha
  have h1 := Subgroup.card_le_of_le hle
  rw [d.card_sup, h.hyp.card] at h1
  have hp := h.hyp.prime.two_le
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem Data.sup_sup_zpowers_eq (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) : (E ⊔ Subgroup.zpowers f) ⊔ Subgroup.zpowers e = A := by
  have hθ := h.hyp.nearFunctor
  have he1 : e ≠ 1 := fun h1 => hen (h1 ▸ one_mem _)
  have hce : Nat.card (Subgroup.zpowers e) = p := by
    rw [(zpowers_mem_signalizerFunctorEk_one hθ.prime hθ.elemAbelian he he1).2, pow_one]
  have hnle : ¬ Subgroup.zpowers e ≤ E ⊔ Subgroup.zpowers f := fun hle =>
    hen (hle (Subgroup.mem_zpowers e))
  have hd := inf_eq_bot_of_not_le hθ.prime hce hnle
  have hcard : Nat.card ((E ⊔ Subgroup.zpowers f) ⊔ Subgroup.zpowers e : Subgroup G) = p ^ 3 := by
    rw [card_sup_of_commute (fun x hx y hy => comm_of_mem_of_isMulCommutative hθ.elemAbelian.1
      (d.sup_le hx) (Subgroup.zpowers_le.mpr he hy)) hd, d.card_sup, hce]
    ring
  exact Subgroup.eq_of_le_of_card_ge (_root_.sup_le d.sup_le (Subgroup.zpowers_le.mpr he))
    (by rw [hcard, h.hyp.card])

omit [Finite G] in
theorem zpow_mem_iff_dvd {S : Subgroup G} (hp : p.Prime) {e : G} (hep : e ^ p = 1) (hen : e ∉ S)
    (k : ℤ) : e ^ k ∈ S ↔ (p : ℤ) ∣ k := by
  constructor
  · intro hk
    by_contra hpk
    exact hen (Sec6Gen.mem_of_zpow_mem hp hep hpk hk)
  · rintro ⟨m, rfl⟩
    have : e ^ ((p : ℤ) * m) = 1 := by
      rw [zpow_mul, zpow_natCast, hep, one_zpow]
    rw [this]
    exact one_mem _

end Orbit

section Components

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem commute_dsub_A (h : Counterexample p A θ) :
    ∀ x ∈ dsub A θ, ∀ y ∈ A, Commute x y := fun _ hx y hy =>
  (Subgroup.mem_centralizer_iff.mp (dsub_le_centralizer h.hyp.nearFunctor hx) y hy).symm

theorem Data.exists_conj
    (d : Data h E f) {J L : Subgroup G} (hJ : J ∈ lcal (θ f))
    (hL : L ∈ lcal (θ f)) :
    ∃ x ∈ dsub A θ, ∃ a ∈ A, L = J.map (MulAut.conj (x * a)).toMonoidHom := by
  have hthe := h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one
  obtain ⟨g, hg, hLg⟩ := Sec6S31.exists_conj h d.zpowers_mem_rSet
    (by rw [hthe, d.lcal_kOf]; exact hJ) (by rw [hthe, d.lcal_kOf]; exact hL)
  obtain ⟨x, hx, a, ha, rfl⟩ := (mem_sup_iff_of_commute (commute_dsub_A h)).mp hg
  exact ⟨x, hx, a, ha, hLg⟩

theorem Data.inf_normalizer_eq
    (d : Data h E f) {J : Subgroup G} (hJ : J ∈ lcal (θ f)) :
    A ⊓ Subgroup.normalizer (J : Set G) = E ⊔ Subgroup.zpowers f := by
  have hθ := h.hyp.nearFunctor
  apply le_antisymm
  · rintro a ⟨haA, haJ⟩
    rw [d.mem_sup_iff haA]
    intro L hL
    obtain ⟨x, hx, a', ha', rfl⟩ := d.exists_conj hJ hL
    have hJa : J.map (MulAut.conj a).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haJ
    have hxa : a * x = x * a := (commute_dsub_A h x hx a haA).eq.symm
    have haa' : a * a' = a' * a := comm_of_mem_of_isMulCommutative hθ.elemAbelian.1 haA ha'
    have hag : a * (x * a') = (x * a') * a := by
      calc a * (x * a') = (a * x) * a' := by rw [mul_assoc]
        _ = (x * a) * a' := by rw [hxa]
        _ = x * (a * a') := by rw [mul_assoc]
        _ = x * (a' * a) := by rw [haa']
        _ = (x * a') * a := by rw [mul_assoc]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc (J.map (MulAut.conj (x * a')).toMonoidHom).map (MulAut.conj a).toMonoidHom
        = J.map (MulAut.conj (a * (x * a'))).toMonoidHom := map_conj_map_conj J _ _
      _ = J.map (MulAut.conj ((x * a') * a)).toMonoidHom := by rw [hag]
      _ = (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj (x * a')).toMonoidHom :=
          (map_conj_map_conj J _ _).symm
      _ = J.map (MulAut.conj (x * a')).toMonoidHom := by rw [hJa]
  · intro a ha
    exact ⟨d.sup_le ha, (d.mem_sup_iff (d.sup_le ha)).mp ha J hJ⟩

theorem Data.exists_zpow_conj
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) {J L : Subgroup G} (hJ : J ∈ lcal (θ f))
    (hL : L ∈ lcal (θ f)) : ∃ k : ℤ, L = J.map (MulAut.conj (e ^ k)).toMonoidHom := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨x, hx, a, ha, hLa⟩ := d.exists_conj hJ hL
  have ha' : a ∈ (E ⊔ Subgroup.zpowers f) ⊔ Subgroup.zpowers e := by
    rw [d.sup_sup_zpowers_eq he hen]
    exact ha
  obtain ⟨n, hn, y, hy, rfl⟩ := (mem_sup_iff_of_commute (fun u hu v hv =>
    comm_of_mem_of_isMulCommutative hθ.elemAbelian.1 (d.sup_le hu)
      (Subgroup.zpowers_le.mpr he hv))).mp ha'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨k, ?_⟩
  have hAH : A ≤ Subgroup.normalizer (θ f : Set G) := hθ.isFunctor.normalized f d.mem d.ne_one
  have hJ' : J.map (MulAut.conj (e ^ k)).toMonoidHom ∈ lcal (θ f) :=
    map_conj_mem_lcal hJ (hAH (zpow_mem he k))
  have hxn : x * n ∈ Subgroup.normalizer ((J.map (MulAut.conj (e ^ k)).toMonoidHom : Subgroup G)
      : Set G) :=
    mul_mem (d.mem_normalizer_of_mem (dsub_le_apply d.mem d.ne_one hx) hJ')
      ((d.mem_sup_iff (d.sup_le hn)).mp hn _ hJ')
  rw [hLa]
  calc J.map (MulAut.conj (x * (n * e ^ k))).toMonoidHom
      = (J.map (MulAut.conj (e ^ k)).toMonoidHom).map (MulAut.conj (x * n)).toMonoidHom := by
        rw [map_conj_map_conj, mul_assoc]
    _ = J.map (MulAut.conj (e ^ k)).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxn

omit [Finite G] in
theorem nonempty_mulEquiv_piCongrLeft {ι ι' : Type*} (φ : ι → Type*) [∀ i, Mul (φ i)]
    (e : ι' ≃ ι) : Nonempty ((∀ i', φ (e i')) ≃* ∀ i, φ i) :=
  ⟨{ toEquiv := Equiv.piCongrLeft φ e
     map_mul' := fun x y => by
       funext i
       obtain ⟨i', rfl⟩ := e.surjective i
       simp [Equiv.piCongrLeft_apply_apply] }⟩

theorem Data.conj_pow_eq_iff
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) {J : Subgroup G} (hJ : J ∈ lcal (θ f)) {k l : ℤ}
    (hkl : J.map (MulAut.conj (e ^ k)).toMonoidHom = J.map (MulAut.conj (e ^ l)).toMonoidHom) :
    (p : ℤ) ∣ k - l := by
  have hθ := h.hyp.nearFunctor
  have h1 : (J.map (MulAut.conj (e ^ k)).toMonoidHom).map (MulAut.conj (e ^ (-l))).toMonoidHom
      = J := by
    rw [hkl, map_conj_map_conj, ← zpow_add, neg_add_cancel, zpow_zero]
    ext x
    simp
  rw [map_conj_map_conj, ← zpow_add] at h1
  have hmem : e ^ (-l + k) ∈ A ⊓ Subgroup.normalizer (J : Set G) :=
    ⟨zpow_mem he _, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1⟩
  rw [d.inf_normalizer_eq hJ] at hmem
  have := (zpow_mem_iff_dvd hθ.prime (hθ.elemAbelian.2 e he) hen _).mp hmem
  rwa [neg_add_eq_sub] at this

end Components

section Pi

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.nonempty_equiv_fin
    (d : Data h E f) : Nonempty (Fin p ≃ ↥(lcal (θ f))) := by
  classical
  have hθ := h.hyp.nearFunctor
  obtain ⟨J, hJ⟩ := d.lcal_nonempty
  obtain ⟨e, he, hen⟩ := d.exists_mem_sdiff
  have hAH : A ≤ Subgroup.normalizer (θ f : Set G) := hθ.isFunctor.normalized f d.mem d.ne_one
  have hep : e ^ p = 1 := hθ.elemAbelian.2 e he
  let ι : Fin p → Subgroup G := fun i => J.map (MulAut.conj (e ^ (i : ℕ))).toMonoidHom
  have hι_mem : ∀ i, ι i ∈ lcal (θ f) := fun i =>
    map_conj_mem_lcal hJ (hAH (pow_mem he _))
  have hι_inj : Function.Injective ι := by
    intro i j hij
    have hd := d.conj_pow_eq_iff he hen hJ (k := (i : ℕ)) (l := (j : ℕ)) (by
      simpa only [zpow_natCast] using hij)
    have hi := i.2
    have hj := j.2
    refine Fin.ext ?_
    have h1 : ((j : ℕ) : ℤ) % p = ((i : ℕ) : ℤ) % p := Int.modEq_iff_dvd.mpr hd
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)] at h1
    exact_mod_cast h1.symm
  have hι_surj : ∀ L ∈ lcal (θ f), ∃ i, ι i = L := by
    intro L hL
    obtain ⟨k, hk⟩ := d.exists_zpow_conj he hen hJ hL
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hθ.prime.pos
    refine ⟨⟨(k % p).toNat, ?_⟩, ?_⟩
    · have := Int.emod_lt_of_pos k hp0
      have h0 := Int.emod_nonneg k hp0.ne'
      omega
    · show J.map (MulAut.conj (e ^ (k % p).toNat)).toMonoidHom = L
      rw [hk]
      congr 2
      have h0 := Int.emod_nonneg k hp0.ne'
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
      conv_rhs => rw [← Int.emod_add_mul_ediv k p]
      rw [zpow_add, zpow_mul, zpow_natCast, hep, one_zpow, mul_one]
  exact ⟨Equiv.ofBijective (fun i => (⟨ι i, hι_mem i⟩ : lcal (θ f)))
    ⟨fun i j hij => hι_inj (congrArg Subtype.val hij), fun L => by
      obtain ⟨i, hi⟩ := hι_surj L.1 L.2
      exact ⟨i, Subtype.ext hi⟩⟩⟩

theorem Data.nonempty_mulEquiv_pi
    (d : Data h E f) {f₀ : G} (d₀ : Data h E f₀)
    {J₀ : Subgroup G} (hJ₀ : J₀ ∈ lcal (θ f₀)) :
    Nonempty (↥(kOf (θ f)) ≃* (Fin p → ↥J₀)) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨σ⟩ := d.nonempty_equiv_fin
  have hiso : ∀ i : Fin p, Nonempty (↥((σ i : lcal (θ f)) : Subgroup G) ≃* ↥J₀) := by
    intro i
    have hthe := hθ.isFunctor.thetaOf_zpowers d.mem d.ne_one
    have hthe₀ := hθ.isFunctor.thetaOf_zpowers d₀.mem d₀.ne_one
    exact h.lemma610 d.zpowers_mem_rSet d₀.zpowers_mem_rSet (by rw [hthe]; exact (σ i).2)
      (by rw [hthe₀]; exact hJ₀)
  obtain ⟨e2⟩ := nonempty_mulEquiv_piCongrLeft (fun L : lcal (θ f) => ↥(L : Subgroup G)) σ
  exact ⟨((d.isDirectProduct.equiv).symm.trans e2.symm).trans
    (MulEquiv.piCongrRight fun i => (hiso i).some)⟩

end Pi

section Plane

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.perfRes_eq
    (d : Data h E f) : perfRes (θ f) = kOf (θ f) := by
  have hthe := h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one
  have := h.perfRes_thetaOf_eq_kOf (B := Subgroup.zpowers f)
    (fun hb => d.ne_one (Subgroup.zpowers_eq_bot.mp hb)) (Subgroup.zpowers_le.mpr d.mem)
    (by rw [hthe]; exact d.not_isSolvable)
  rwa [hthe] at this

theorem Data.coord_bijective
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) {J : Subgroup G} (hJ : J ∈ lcal (θ f)) :
    Function.Bijective ((d.isDirectProduct.coord hJ).comp (Subgroup.inclusion
      (inf_le_left : kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G) ≤ kOf (θ f)))) := by
  have hθ := h.hyp.nearFunctor
  have hD := d.isDirectProduct
  have hAH : A ≤ Subgroup.normalizer (θ f : Set G) := hθ.isFunctor.normalized f d.mem d.ne_one
  have hconj : ∀ a ∈ Subgroup.zpowers e, ∀ J' ∈ lcal (θ f),
      J'.map (MulAut.conj a).toMonoidHom ∈ lcal (θ f) := fun a ha J' hJ' =>
    map_conj_mem_lcal hJ' (hAH (Subgroup.zpowers_le.mpr he ha))
  have htrans : ∀ K' ∈ lcal (θ f), ∃ a ∈ Subgroup.zpowers e,
      K' = J.map (MulAut.conj a).toMonoidHom := by
    intro K' hK'
    obtain ⟨k, hk⟩ := d.exists_zpow_conj he hen hJ hK'
    exact ⟨e ^ k, Subgroup.zpow_mem_zpowers e k, hk⟩
  have hcent : Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) =
      Subgroup.centralizer ({e} : Set G) := centralizer_zpowers_eq_singleton e
  have hinj := inf_centralizer_inf_sSup_eq_bot_of_transitive hD hconj hJ htrans
  have hproj := projIn_centralizer_eq hD hconj hJ
  have hN : Subgroup.zpowers e ⊓ Subgroup.normalizer (J : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxN⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxA : e ^ k ∈ A ⊓ Subgroup.normalizer (J : Set G) := ⟨zpow_mem he k, hxN⟩
    rw [d.inf_normalizer_eq hJ] at hxA
    obtain ⟨m, hm⟩ := (zpow_mem_iff_dvd hθ.prime (hθ.elemAbelian.2 e he) hen k).mp hxA
    rw [Subgroup.mem_bot, hm, zpow_mul, zpow_natCast, hθ.elemAbelian.2 e he, one_zpow]
  rw [hN] at hproj
  have hJ1 : J ⊓ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = J :=
    inf_eq_left.mpr fun x _ => Subgroup.mem_centralizer_iff.mpr fun g hg => by
      have : g = 1 := hg
      subst this
      simp
  rw [hJ1] at hproj
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hx1' : d.isDirectProduct.coord hJ ⟨x, hx.1⟩ = 1 := hx1
    have h1 := (d.isDirectProduct.coord_eq_one_iff hJ ⟨x, hx.1⟩).mp hx1'
    have h2 : x ∈ kOf (θ f) ⊓ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) ⊓
        sSup (lcal (θ f) \ {J}) := ⟨⟨hx.1, hcent ▸ hx.2⟩, h1⟩
    rw [hinj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  · intro j
    have hj : (j : G) ∈ projIn (lcal (θ f)) J (kOf (θ f) ⊓
        Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G)) := by
      rw [hproj]
      exact j.2
    obtain ⟨y, hy, hyj⟩ := (hD.mem_projIn_iff hJ).mp hj
    refine ⟨⟨(y : G), hy.1, hcent ▸ hy.2⟩, Subtype.ext ?_⟩
    exact hyj

omit [Finite G] in
theorem ne_one_of_not_mem_sup {S : Subgroup G} {e : G} (hen : e ∉ S) : e ≠ 1 :=
  fun h1 => hen (h1 ▸ one_mem _)

theorem Data.card_plane (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) :
    Nat.card (Subgroup.zpowers f ⊔ Subgroup.zpowers e : Subgroup G) = p ^ 2 := by
  have hθ := h.hyp.nearFunctor
  have hce : Nat.card (Subgroup.zpowers e) = p :=
    Sec6Gen.card_zpowers_of_pow_eq_one hθ.prime (hθ.elemAbelian.2 e he)
      (ne_one_of_not_mem_sup hen)
  have hnle : ¬ Subgroup.zpowers e ≤ Subgroup.zpowers f := fun hle =>
    hen (Subgroup.mem_sup_right (hle (Subgroup.mem_zpowers e)))
  have hd := inf_eq_bot_of_not_le hθ.prime hce hnle
  rw [card_sup_of_commute (fun x hx y hy => comm_of_mem_of_isMulCommutative hθ.elemAbelian.1
    (Subgroup.zpowers_le.mpr d.mem hx) (Subgroup.zpowers_le.mpr he hy)) hd, d.card_zpowers,
    hce, sq]

theorem Data.plane_le (d : Data h E f) {e : G} (he : e ∈ A) :
    Subgroup.zpowers f ⊔ Subgroup.zpowers e ≤ A :=
  _root_.sup_le (Subgroup.zpowers_le.mpr d.mem) (Subgroup.zpowers_le.mpr he)

theorem Data.thetaOf_plane (d : Data h E f) {e : G} (he : e ∈ A) :
    thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e) = θ f ⊓ Subgroup.centralizer {e} := by
  rw [← h.hyp.isFunctor.inf_centralizer_eq_thetaOf d.mem d.ne_one (Subgroup.zpowers_le.mpr he),
    centralizer_zpowers_eq_singleton]

theorem Data.not_isSolvable_cen
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) :
    ¬ Group.IsSolvable ↥(kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G)) := by
  intro hsol
  obtain ⟨J, hJ⟩ := d.lcal_nonempty
  exact not_isSolvable_of_mem_lcal hJ
    (Group.isSolvable_of_surjective (d.coord_bijective he hen hJ).2)

theorem Data.plane_mem_rSetN_two
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) :
    Subgroup.zpowers f ⊔ Subgroup.zpowers e ∈ rSetN p A θ 2 := by
  refine h.mem_rSetN_iff.mpr ⟨?_, d.plane_le he, ?_, d.card_plane he hen⟩
  · intro hbot
    exact d.ne_one (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp (hbot ▸ le_sup_left)))
  · rw [d.thetaOf_plane he]
    intro hsol
    have hle : kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G) ≤
        θ f ⊓ Subgroup.centralizer {e} := inf_le_inf_right _ (kOf_le (θ f))
    have := hsol
    exact d.not_isSolvable_cen he hen (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hle))

theorem Data.cen_mem_lcal
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) :
    kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G) ∈
      lcal (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e)) := by
  obtain ⟨J, hJ⟩ := d.lcal_nonempty
  obtain ⟨-, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
  let φ := MulEquiv.ofBijective _ (d.coord_bijective he hen hJ)
  have hle : kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e) := by
    rw [d.thetaOf_plane he]
    exact inf_le_inf_right _ (kOf_le (θ f))
  have hnorm : thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e) ≤ Subgroup.normalizer
      ((kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) := by
    rw [d.thetaOf_plane he]
    exact (Admits.inf (inf_le_left.trans (Thm41Aux.le_normalizer_kOf (θ f)) :
      Admits (θ f ⊓ Subgroup.centralizer {e}) (kOf (θ f)))
      (inf_le_right.trans Subgroup.le_normalizer :
        Admits (θ f ⊓ Subgroup.centralizer {e}) (Subgroup.centralizer {e})))
  refine mem_lcal_iff.mpr ⟨hle,
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm).isSubnormal, ?_, ?_⟩
  · have := hJs
    exact φ.isSimpleGroup
  · exact fun hcomm => hJnc ((isMulCommutative_congr φ).mp hcomm)

theorem Data.kOf_plane
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) :
    kOf (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e)) =
      kOf (θ f) ⊓ Subgroup.centralizer ({e} : Set G) := by
  have hBR : Subgroup.zpowers f ⊔ Subgroup.zpowers e ∈ rSet p A θ :=
    (d.plane_mem_rSetN_two he hen).1
  have hHB := d.thetaOf_plane he
  have hsolB := Sec6S31.sol_thetaOf_eq_bot h hBR
  obtain ⟨hB1, hBA, hns⟩ := h.mem_rSet_iff.mp hBR
  apply le_antisymm
  · have h1 : kOf (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e)) =
        perfRes (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e)) :=
      (h.perfRes_thetaOf_eq_kOf hB1 hBA hns).symm
    refine le_inf ?_ ?_
    · rw [h1, ← d.perfRes_eq]
      exact Sec6S33.perfRes_mono (thetaOf_le_apply (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers f)) d.ne_one)
    · exact (kOf_le _).trans (hHB ▸ inf_le_right)
  · have := (isDirectProduct_lcal_kOf hsolB).sSup_eq
    rw [← this]
    exact le_sSup (d.cen_mem_lcal he hen)

theorem Data.kOf_plane_mem_lcal
    (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) :
    kOf (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e)) ∈
      lcal (kOf (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e))) := by
  have hBR : Subgroup.zpowers f ⊔ Subgroup.zpowers e ∈ rSet p A θ :=
    (d.plane_mem_rSetN_two he hen).1
  have hsolB := Sec6S31.sol_thetaOf_eq_bot h hBR
  rw [(isSemisimple_kOf hsolB).lcal_eq, simpleComponents_kOf hsolB, d.kOf_plane he hen]
  exact d.cen_mem_lcal he hen


end Plane

omit [Finite G] in
theorem isFrobeniusWithKernel_map {X Y : Type*} [Group X] [Group Y] {H K : Subgroup X}
    (ι : X →* Y) (hι : Function.Injective ι) (hF : IsFrobeniusWithKernel H K) :
    IsFrobeniusWithKernel (H.map ι) (K.map ι) := by
  obtain ⟨hK1, hKH, hKn, V, hV1, hVH, hdis, hsup, hfpf⟩ := hF
  refine ⟨?_, Subgroup.map_mono hKH, ?_, V.map ι, ?_, Subgroup.map_mono hVH, ?_, ?_, ?_⟩
  · exact fun h0 => hK1 ((Subgroup.map_eq_bot_iff_of_injective K hι).mp h0)
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKH)]
    rintro _ _ ⟨k, hk, rfl⟩ ⟨a, ha, rfl⟩
    exact ⟨a * k * a⁻¹, (Subgroup.normal_subgroupOf_iff hKH).mp hKn k a hk ha, by simp⟩
  · exact fun h0 => hV1 ((Subgroup.map_eq_bot_iff_of_injective V hι).mp h0)
  · rw [disjoint_iff, ← Subgroup.map_inf_eq _ _ ι hι, disjoint_iff.mp hdis, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, hsup]
  · rintro _ ⟨v, hv, rfl⟩ hv1 _ ⟨k, hk, rfl⟩ hvk
    have hv1' : v ≠ 1 := fun h1 => hv1 (by rw [h1, map_one])
    have := hfpf v hv hv1' k hk (hι (by rw [map_mul, map_mul]; exact hvk))
    rw [this, map_one]

section Frobenius

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.frobenius
    (d : Data h E f) :
    IsFrobeniusWithKernel (dZero p A θ) (dOne p A θ) ∧
      IsFrobeniusWithKernel (dTwo p A θ) (dOne p A θ) := by
  obtain ⟨e, he, hen⟩ := d.exists_mem_sdiff
  have hBR : Subgroup.zpowers f ⊔ Subgroup.zpowers e ∈ rSet p A θ :=
    (d.plane_mem_rSetN_two he hen).1
  set B := Subgroup.zpowers f ⊔ Subgroup.zpowers e with hB
  have hX := Sec6S31.mem_mtil h hBR
  have hK := (Sec6S31.hyp h hBR).semisimpleAction
  have hJ := d.kOf_plane_mem_lcal he hen
  obtain ⟨φ, hφ, hC, hC₀, -, -⟩ := hK.exists_frame_data hJ
  have hNS := hK.nearSimple hJ
  obtain ⟨hF1, hF2, -, -, -⟩ := near_frobenius hNS hφ
  have hnor : norIn A (kOf (thetaOf θ B)) = A :=
    inf_eq_left.mpr (Thm41Aux.admits_kOf hX.1.1)
  rw [hnor, Sec6S31.cenIn_kOf_eq h hBR] at hC
  rw [hnor, Sec6S31.cenIn_kOf_eq h hBR] at hC₀
  have hinj := (kOf (thetaOf θ B)).subtype_injective
  refine ⟨?_, ?_⟩
  · have := isFrobeniusWithKernel_map (kOf (thetaOf θ B)).subtype hinj hF2
    rwa [hC, hC₀] at this
  · have := isFrobeniusWithKernel_map (kOf (thetaOf θ B)).subtype hinj hF1
    have h2 : (fixedCore1 φ).map (kOf (thetaOf θ B)).subtype = dTwo p A θ := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hcD : (c : G) ∈ dZero p A θ := hC ▸ ⟨c, hc.1, rfl⟩
        refine ⟨hcD, mem_sectionCentralizer_iff.mpr ⟨?_, Subgroup.le_normalizer hcD, ?_⟩⟩
        · exact Thm210.le_normalizer_fittingSubgroupOf (dZero p A θ) hcD
        · intro y hy
          obtain ⟨y', hy', rfl⟩ : y ∈ (signalizerFixedSubgroup φ).map
              (kOf (thetaOf θ B)).subtype := hC ▸ hy
          have hmem := hc.2 y' hy'
          show ((⁅c, y'⁆ : kOf (thetaOf θ B)) : G) ∈ dOne p A θ
          have h3 : ((⁅c, y'⁆ : kOf (thetaOf θ B)) : G) ∈
              (fixedFitting φ).map (kOf (thetaOf θ B)).subtype := ⟨⁅c, y'⁆, hmem, rfl⟩
          rw [hC₀] at h3
          exact h3
      · intro hx
        obtain ⟨c, hcC, rfl⟩ : x ∈ (signalizerFixedSubgroup φ).map (kOf (thetaOf θ B)).subtype :=
          hC ▸ hx.1
        refine ⟨c, ⟨hcC, fun y' hy' => ?_⟩, rfl⟩
        have hy'D : ((y' : kOf (thetaOf θ B)) : G) ∈ dZero p A θ := hC ▸ ⟨y', hy', rfl⟩
        have h3 : ((⁅c, y'⁆ : kOf (thetaOf θ B)) : G) ∈ dOne p A θ :=
          (mem_sectionCentralizer_iff.mp hx.2).2.2 _ hy'D
        have h3' : ((⁅c, y'⁆ : kOf (thetaOf θ B)) : G) ∈
            (fixedFitting φ).map (kOf (thetaOf θ B)).subtype := by
          rw [hC₀]
          exact h3
        obtain ⟨z, hz, hzc⟩ := h3'
        
        have : z = ⁅c, y'⁆ := Subtype.ext hzc
        exact this ▸ hz
    rwa [h2, hC₀] at this


end Frobenius

theorem exists_mem_not_mem (h : Counterexample p A θ) {E : Subgroup G} (hE : DistE p A θ E) :
    ∃ f ∈ A, f ∉ E := by
  by_contra hcon
  push Not at hcon
  have hle : A ≤ E := fun a ha => hcon a ha
  have h1 := Subgroup.card_le_of_le hle
  rw [hE.mem.2, h.hyp.card] at h1
  have hp := h.hyp.prime.two_le
  have : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end Sec6S34

end CFSG.SignalizerFunctorTheorem.McBride.Near
