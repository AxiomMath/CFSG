module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneRetoralExact

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ntp_untw_retoralize_exact
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (f : ℕ) (hf : 1 ≤ f)
    (S : LangSetup .E6 L p₀) (hq : S.D.q = 2 ^ f) (hal : S.IsAlgebraic)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (x : S.D.model) {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L)
    {a : Fin Tag.E6.rank → Lˣ}
    (hca : c * (x : ModGL .E6 L) * c⁻¹ = rootDiagUnit .E6 a) :
    ∃ D' : LangDatum .E6 L, D'.q = S.D.q ∧ D'.Φ = S.D.Φ ∧ Finite D'.model ∧
      D'.model = S.D.model.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
      D'.Γ = S.Γ.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom ∧
      (D'.g0⁻¹ * S.D.g0) * (x : ModGL .E6 L) * (D'.g0⁻¹ * S.D.g0)⁻¹ =
        rootDiagUnit .E6 a ∧
      rootDiagUnit .E6 a ∈ D'.torus := by
  classical
  set y : ModGL Tag.E6 L := S.D.g0 * (x : ModGL Tag.E6 L) * S.D.g0⁻¹ with hydef
  have hyfix : y ∈ S.D.fix := by
    rw [← LangDatum.map_conj_model S.D]
    exact ⟨(x : ModGL Tag.E6 L), x.2, by
      show (MulAut.conj S.D.g0) (x : ModGL Tag.E6 L) = y
      rw [MulAut.conj_apply, hydef]⟩
  have hyΦ : S.D.Φ y = y := (LangDatum.mem_fix S.D).1 hyfix |>.2
  obtain ⟨hch, _⟩ :=
    S.exists_charP_isAlgebraic_zmod hal Nat.prime_two (by omega) hq
  haveI := hch
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext cc
    rw [iterateFrobenius_def, hFr]
  have hFrobFr : entrywiseFrobGL Tag.E6 L 2 f = Units.map (entrywiseHom Fr) := by
    change Units.map (entrywiseHom (iterateFrobenius L 2 f)) = Units.map (entrywiseHom Fr)
    rw [← hFr_eq]
  have hyFixed : entrywiseFrobGL Tag.E6 L 2 f y = y := by
    rw [hFrobFr, ← hΦ]
    exact hyΦ
  set g : ModGL Tag.E6 L := S.D.g0 * c⁻¹ with hgdef
  have hgAdj : g ∈ adjointGroup Tag.E6 L := mul_mem S.D.g0_mem (inv_mem hc)
  have hgy : g⁻¹ * y * g = rootDiagUnit Tag.E6 a := by
    rw [hgdef, hydef]
    calc (S.D.g0 * c⁻¹)⁻¹ * (S.D.g0 * (x : ModGL Tag.E6 L) * S.D.g0⁻¹) *
          (S.D.g0 * c⁻¹)
        = c * (x : ModGL Tag.E6 L) * c⁻¹ := by group
      _ = rootDiagUnit Tag.E6 a := hca
  have hNpos : 0 < Nat.card S.D.model := by
    haveI : Finite S.D.model := S.finite
    exact Finite.card_pos_iff.mpr ⟨1⟩
  have hxN : (x : ModGL Tag.E6 L) ^ Nat.card S.D.model = 1 :=
    (orderOf_dvd_iff_pow_eq_one).1 (Subgroup.orderOf_dvd_natCard S.D.model x.2)
  have hyN : y ^ Nat.card S.D.model = 1 := by
    rw [hydef, conj_pow, hxN, mul_one, mul_inv_cancel]
  have hdaN : rootDiagUnit Tag.E6 a ^ Nat.card S.D.model = 1 := by
    rw [← hgy]
    have hc := conj_pow (a := g⁻¹) (b := y) (i := Nat.card S.D.model)
    rw [inv_inv, hyN, mul_one, inv_mul_cancel] at hc
    exact hc
  let p : ℕ := orderOf (rootDiagUnit Tag.E6 a)
  have hmne : p ≠ 0 := by
    have hdvdN : p ∣ Nat.card S.D.model := orderOf_dvd_of_pow_eq_one hdaN
    intro hp0
    rw [hp0] at hdvdN
    exact hNpos.ne' (Nat.eq_zero_of_zero_dvd hdvdN)
  have hpodd : Odd p := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    rw [even_iff_exists_two_mul] at heven
    obtain ⟨k, hk⟩ := heven
    have hdm : (rootDiagUnit Tag.E6 a) ^ p = 1 := pow_orderOf_eq_one _
    have hdk2 : ((rootDiagUnit Tag.E6 a) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm k 2, ← hk, hdm]
    have hrootpowk : (rootDiagUnit Tag.E6 a) ^ k = rootDiagUnit Tag.E6 (a ^ k) :=
      (map_pow (rootDiagUnitHom Tag.E6 L) a k).symm
    have hsq : (rootDiagUnit Tag.E6 (a ^ k)) ^ 2 = 1 := by
      rw [← hrootpowk]
      exact hdk2
    have hb2 : (a ^ k) ^ 2 = 1 :=
      (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L))
        (by
          change rootDiagUnitHom Tag.E6 L ((a ^ k) ^ 2) = rootDiagUnitHom Tag.E6 L 1
          rw [map_pow (rootDiagUnitHom Tag.E6 L) (a ^ k) 2,
            map_one (rootDiagUnitHom Tag.E6 L)]
          exact hsq)
    have hak : a ^ k = 1 := by
      funext i
      apply Units.ext
      have hUnit : ((a i) ^ k) ^ 2 = 1 := by
        have hh := congrFun hb2 i
        simpa [Pi.pow_apply] using hh
      have hco : (((a i) ^ k : Lˣ) : L) ^ 2 = 1 := by
        have h := congrArg (fun u : Lˣ => (u : L)) hUnit
        rw [Units.val_pow_eq_pow_val, Units.val_one] at h
        exact h
      rcases sq_eq_one_iff.mp hco with h | h
      · exact h
      · rwa [CharTwo.neg_eq 1] at h
    have hdk1 : (rootDiagUnit Tag.E6 a) ^ k = 1 := by
      rw [hrootpowk, hak, rootDiagUnit_one]
    have hdvd : p ∣ k := orderOf_dvd_of_pow_eq_one hdk1
    have hkpos : 0 < k := by omega
    have hle : p ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have hpq : Nat.Coprime p (2 ^ f) := (Odd.coprime_two_right hpodd).pow_right f
  have hrootpow : (rootDiagUnit Tag.E6 a) ^ p = rootDiagUnit Tag.E6 (a ^ p) :=
    (map_pow (rootDiagUnitHom Tag.E6 L) a p).symm
  have hap : a ^ p = 1 :=
    (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L))
      (by rw [← hrootpow, pow_orderOf_eq_one, rootDiagUnit_one])
  let afam : Unit → Fin Tag.E6.rank → Lˣ := fun _ => a
  have hexp : ∀ s : Unit, ∀ i, afam s i ^ p = 1 := by
    intro s i
    have h := congrFun hap i
    simpa [afam, Pi.pow_apply] using h
  have hn : ∀ s : Unit,
      (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g) *
        entrywiseFrobGL Tag.E6 L 2 f
          (rootDiagUnit Tag.E6 (afam s)) *
        (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g)⁻¹ =
        rootDiagUnit Tag.E6 (afam s) := by
    intro s
    rcases s with ⟨⟩
    show (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g) *
          entrywiseFrobGL Tag.E6 L 2 f (rootDiagUnit Tag.E6 a) *
          (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g)⁻¹ =
        rootDiagUnit Tag.E6 a
    have hF : entrywiseFrobGL Tag.E6 L 2 f (rootDiagUnit Tag.E6 a) =
        (entrywiseFrobGL Tag.E6 L 2 f g)⁻¹ * y *
          entrywiseFrobGL Tag.E6 L 2 f g := by
      rw [← hgy, map_mul, map_mul, map_inv, hyFixed]
    calc (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g) *
          entrywiseFrobGL Tag.E6 L 2 f (rootDiagUnit Tag.E6 a) *
          (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g)⁻¹
        = (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g) *
          ((entrywiseFrobGL Tag.E6 L 2 f g)⁻¹ * y *
            entrywiseFrobGL Tag.E6 L 2 f g) *
          (g⁻¹ * entrywiseFrobGL Tag.E6 L 2 f g)⁻¹ := by rw [hF]
      _ = g⁻¹ * y * g := by group
      _ = rootDiagUnit Tag.E6 a := hgy
  obtain ⟨w', z, hz, hlang⟩ :=
    exists_lang_datum_of_plane 2 f hf hpq afam hexp hgAdj hn
  have hzC := familyGroup_le_familyCentralizer (K := L) afam hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hza : rootDiagUnit Tag.E6 a * z = z * rootDiagUnit Tag.E6 a := by
    have h := hzcomm ()
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hzd : z⁻¹ * rootDiagUnit Tag.E6 a * z = rootDiagUnit Tag.E6 a := by
    calc z⁻¹ * rootDiagUnit Tag.E6 a * z
        = z⁻¹ * (rootDiagUnit Tag.E6 a * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit Tag.E6 a) := by rw [hza]
      _ = rootDiagUnit Tag.E6 a := by group
  set g₁ : ModGL Tag.E6 L := g * z with hg₁def
  have hg₁Adj : g₁ ∈ adjointGroup Tag.E6 L := mul_mem hgAdj hzG
  have hLang₁ : entrywiseFrobGL Tag.E6 L 2 f g₁ =
      g₁ * canonicalRep (coxeterSystem Tag.E6) L w' := by
    exact inv_mul_eq_iff_eq_mul.1 hlang
  have hg₁y : g₁⁻¹ * y * g₁ = rootDiagUnit Tag.E6 a := by
    rw [hg₁def]
    calc (g * z)⁻¹ * y * (g * z) = z⁻¹ * (g⁻¹ * y * g) * z := by group
      _ = z⁻¹ * rootDiagUnit Tag.E6 a * z := by rw [hgy]
      _ = rootDiagUnit Tag.E6 a := hzd
  have hLang : Units.map (entrywiseHom Fr) g₁ =
      g₁ * canonicalRep (coxeterSystem Tag.E6) L w' := by
    rw [← hFrobFr]
    exact hLang₁
  let D' : LangDatum Tag.E6 L :=
    LangDatum.ofFrobenius Fr (2 ^ f) hFr w' hg₁Adj hLang
  have hD'q : D'.q = S.D.q := by rw [hq]; rfl
  have hD'Φ : D'.Φ = Units.map (entrywiseHom Fr) := rfl
  have hD'n : D'.n = canonicalRep (coxeterSystem Tag.E6) L w' := rfl
  have hD'g0 : D'.g0 = g₁ := rfl
  have hfix_eq : D'.fix = S.D.fix := by
    simp only [LangDatum.fix]
    rw [hD'Φ, hΦ]
  have hD'model : D'.model =
      S.D.model.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom := by
    rw [LangDescent.model_eq D', LangDescent.model_eq S.D, hfix_eq, Subgroup.map_map]
    have hcomp : (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom.comp
        (MulAut.conj S.D.g0⁻¹).toMonoidHom = (MulAut.conj D'.g0⁻¹).toMonoidHom := by
      ext zz
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hcomp]
  have hFinite : Finite D'.model := by
    haveI : Finite S.D.model := S.finite
    rw [hD'model]
    exact Finite.of_surjective
      ((MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom.subgroupMap S.D.model)
      ((MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom.subgroupMap_surjective S.D.model)
  have hD'Γ : D'.Γ = S.Γ.map (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom := by
    have hΓmap : D'.Γ.map (MulAut.conj D'.g0).toMonoidHom =
        S.D.Γ.map (MulAut.conj S.D.g0).toMonoidHom := by
      rw [LangDatum.map_conj_Γ D', LangDatum.map_conj_Γ S.D, hfix_eq]
    have h1 := congrArg (Subgroup.map (MulAut.conj D'.g0⁻¹).toMonoidHom) hΓmap
    rw [Subgroup.map_map, Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id] at h1
    have hcomp : (MulAut.conj D'.g0⁻¹).toMonoidHom.comp (MulAut.conj S.D.g0).toMonoidHom =
        (MulAut.conj (D'.g0⁻¹ * S.D.g0)).toMonoidHom := by
      ext zz
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h1, hcomp]
    rfl
  have hcx : (D'.g0⁻¹ * S.D.g0) * (x : ModGL Tag.E6 L) *
      (D'.g0⁻¹ * S.D.g0)⁻¹ = rootDiagUnit Tag.E6 a := by
    have e : (D'.g0⁻¹ * S.D.g0) * (x : ModGL Tag.E6 L) *
        (D'.g0⁻¹ * S.D.g0)⁻¹ = g₁⁻¹ * y * g₁ := by
      rw [hD'g0, hydef]
      group
    rw [e, hg₁y]
  have hD'torus : D'.torus = twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L w')
      (entrywiseFrobGL Tag.E6 L 2 f) := by
    have h1 : D'.torus = twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L w')
        (Units.map (entrywiseHom Fr)) := by
      simp only [LangDatum.torus, hD'n, hD'Φ]
    rw [h1, hFrobFr]
  have hFr_r : entrywiseFrobGL Tag.E6 L 2 f (rootDiagUnit Tag.E6 a) =
      (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ * rootDiagUnit Tag.E6 a *
        canonicalRep (coxeterSystem Tag.E6) L w' := by
    rw [← hg₁y, map_mul, map_mul, map_inv, hyFixed, hLang₁]
    group
  have htor : rootDiagUnit Tag.E6 a ∈ D'.torus := by
    rw [hD'torus, mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
    rw [hFr_r]
    group
  exact ⟨D', hD'q, hD'Φ.trans hΦ.symm, hFinite, hD'model, hD'Γ, hcx, htor⟩

end CFSG.StandardType.NTPlane

end
