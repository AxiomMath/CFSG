module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusDefs

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.RankThree.PartOne.KE

abbrev l10mp2a_perm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem l10mp2a_weylTuple_simple {L : Type} [Field L] (j : Fin Tag.E6.rank)
    (b : Fin Tag.E6.rank → Lˣ) :
    weylTuple (simple Tag.E6 j) b =
      fun i => b i * b j ^ (-Tag.E6.cartan j i) := by
  have hsum : ∀ i : Fin Tag.E6.rank,
      (∑ x, Tag.E6.cartan j x * (Pi.single i 1 : Fin Tag.E6.rank → ℤ) x) =
        Tag.E6.cartan j i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne hx]
    · intro h; simp at h
  funext i
  rw [← rootChar_single (weylTuple (simple Tag.E6 j) b) i, rootChar_weylTuple, simple_inv,
    simple_smul, reflect, hsum i, rootChar_sub, rootChar_zsmul,
    CFSG.LieType.Chevalley.rootChar_single, CFSG.LieType.Chevalley.rootChar_single]
  simp [zpow_neg]

theorem l10mp2a_cartan_mulSingle {L : Type} [Field L] (j : Fin Tag.E6.rank) (Q : Lˣ) :
    e6RootParams (Pi.mulSingle j Q) = fun i => Q ^ Tag.E6.cartan j i := by
  funext i
  simp only [e6RootParams]
  rw [Finset.prod_eq_single j]
  · simp
  · intro x _ hx
    rw [Pi.mulSingle_eq_of_ne hx, one_zpow]
  · intro h
    simp at h

theorem l10mp2a_cartan_starS {L : Type} [Field L] (j : Fin Tag.E6.rank) (u : Fin Tag.E6.rank → Lˣ) :
    e6RootParams (e6StarS j u) = weylTuple (simple Tag.E6 j) (e6RootParams u) := by
  have hQ : (∏ x, u x ^ (-Tag.E6.cartan x j)) = (e6RootParams u j)⁻¹ := by
    simp only [e6RootParams, zpow_neg]
    rw [Finset.prod_inv_distrib]
  rw [l10mp2a_weylTuple_simple]
  rw [e6StarS]
  have hmul : e6RootParams (u * Pi.mulSingle j (∏ x, u x ^ (-Tag.E6.cartan x j))) =
      e6RootParams u * e6RootParams (Pi.mulSingle j (∏ x, u x ^ (-Tag.E6.cartan x j))) := by
    rw [show e6RootParams (u * Pi.mulSingle j (∏ x, u x ^ (-Tag.E6.cartan x j))) =
        twE6Cartan (u * Pi.mulSingle j (∏ x, u x ^ (-Tag.E6.cartan x j))) from rfl, map_mul]
    rfl
  rw [hmul, l10mp2a_cartan_mulSingle]
  funext i
  simp only [Pi.mul_apply]
  rw [hQ, inv_zpow, zpow_neg]
theorem l10mp2a_cartan_foldr {L : Type} [Field L] (ω : List (Fin Tag.E6.rank))
    (x : Fin Tag.E6.rank → Lˣ) :
    e6RootParams (ω.foldr e6StarS x) =
      weylTuple ((coxeterSystem Tag.E6).wordProd ω) (e6RootParams x) := by
  induction ω generalizing x with
  | nil => rw [List.foldr_nil, CoxeterSystem.wordProd_nil, weylTuple_one]
  | cons j ω ih =>
    rw [List.foldr_cons, CoxeterSystem.wordProd_cons, l10mp2a_cartan_starS, ih,
      ← weylTuple_weylTuple]

theorem l10mp2a_cartan_sigma {L : Type} [Field L] (Fr : L →+* L) (c : Fin Tag.E6.rank → Lˣ) :
    e6RootParams (fun i => Units.map Fr.toMonoidHom (c (l10mp2a_perm i))) =
      fun i => Units.map Fr.toMonoidHom (e6RootParams c (l10mp2a_perm i)) := by
  let p : Equiv.Perm (Fin Tag.E6.rank) := l10mp2a_perm
  change e6RootParams (fun i => Units.map Fr.toMonoidHom (c (p i))) =
    fun i => Units.map Fr.toMonoidHom (e6RootParams c (p i))
  have hcp : ∀ a b : Fin Tag.E6.rank, Tag.E6.cartan (p a) (p b) = Tag.E6.cartan a b :=
    fun a b => TwistTag.cartan_perm TwistTag.E6 a b
  funext i
  simp only [e6RootParams]
  have h1 : (∏ l, (Units.map Fr.toMonoidHom (c (p l))) ^ Tag.E6.cartan l i) =
      ∏ l, (Units.map Fr.toMonoidHom (c (p l))) ^
        Tag.E6.cartan (p l) (p i) := by
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hcp]
  rw [h1]
  have h2 : (∏ l, (Units.map Fr.toMonoidHom (c (p l))) ^
      Tag.E6.cartan (p l) (p i)) =
      ∏ x, (Units.map Fr.toMonoidHom (c x)) ^ Tag.E6.cartan x (p i) := by
    rw [← Equiv.prod_comp p
      (fun x => (Units.map Fr.toMonoidHom (c x)) ^ Tag.E6.cartan x (p i))]
  rw [h2, map_prod]
  exact Finset.prod_congr rfl fun x _ =>
    (map_zpow (Units.map Fr.toMonoidHom) (c x) (Tag.E6.cartan x (p i))).symm

theorem l10mp2a_weylTuple_mul {L : Type} [Field L] (v : WeylGroup Tag.E6)
    (b b' : Fin Tag.E6.rank → Lˣ) :
    weylTuple v (b * b') = weylTuple v b * weylTuple v b' := by
  funext i
  rw [← CFSG.LieType.Chevalley.rootChar_single (weylTuple v (b * b')) i,
    ← CFSG.LieType.Chevalley.rootChar_single (weylTuple v b * weylTuple v b') i]
  rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul]
  rw [rootChar_weylTuple, rootChar_weylTuple, rootChar_weylTuple,
    ← CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul]

theorem l10mp2a_weylTuple_one {L : Type} [Field L] (v : WeylGroup Tag.E6) :
    weylTuple v (1 : Fin Tag.E6.rank → Lˣ) = 1 := by
  funext i
  simp [weylTuple, rootChar]

theorem l10mp2a_weylTuple_inv {L : Type} [Field L] (v : WeylGroup Tag.E6)
    (b : Fin Tag.E6.rank → Lˣ) :
    weylTuple v b⁻¹ = (weylTuple v b)⁻¹ := by
  apply mul_right_cancel (b := weylTuple v b)
  rw [← l10mp2a_weylTuple_mul, inv_mul_cancel, l10mp2a_weylTuple_one, inv_mul_cancel]

@[expose] def l10mp2a_AFix {L : Type} [Field L] (Fr : L →+* L) (v : WeylGroup Tag.E6) :
    Subgroup (Fin Tag.E6.rank → Lˣ) where
  carrier := {a | weylTuple v (fun i => Units.map Fr.toMonoidHom (a (l10mp2a_perm i))) = a}
  mul_mem' {a b} ha hb := by
    change weylTuple v (fun i => Units.map Fr.toMonoidHom ((a * b) (l10mp2a_perm i))) = a * b
    have h : weylTuple v (fun i => Units.map Fr.toMonoidHom ((a * b) (l10mp2a_perm i))) =
        weylTuple v (fun i => Units.map Fr.toMonoidHom (a (l10mp2a_perm i))) *
          weylTuple v (fun i => Units.map Fr.toMonoidHom (b (l10mp2a_perm i))) := by
      rw [← l10mp2a_weylTuple_mul]
      congr 1
      funext i
      simp only [Pi.mul_apply, map_mul]
    rw [h, ha, hb]
  one_mem' := by
    change weylTuple v (fun i => Units.map Fr.toMonoidHom
      ((1 : Fin Tag.E6.rank → Lˣ) (l10mp2a_perm i))) = 1
    have h : (fun i => Units.map Fr.toMonoidHom
        ((1 : Fin Tag.E6.rank → Lˣ) (l10mp2a_perm i))) = 1 := by
      funext i; simp
    calc weylTuple v (fun i => Units.map Fr.toMonoidHom
        ((1 : Fin Tag.E6.rank → Lˣ) (l10mp2a_perm i))) = weylTuple v 1 := by rw [h]
      _ = 1 := l10mp2a_weylTuple_one v
  inv_mem' {a} ha := by
    change weylTuple v (fun i => Units.map Fr.toMonoidHom ((a⁻¹) (l10mp2a_perm i))) = a⁻¹
    have h : weylTuple v (fun i => Units.map Fr.toMonoidHom ((a⁻¹) (l10mp2a_perm i))) =
        (weylTuple v (fun i => Units.map Fr.toMonoidHom (a (l10mp2a_perm i))))⁻¹ := by
      rw [← l10mp2a_weylTuple_inv]
      congr 1
    rw [h]
    exact congrArg Inv.inv ha

theorem l10mp2a_cartan_fp {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank))
    (c : Fin Tag.E6.rank → Lˣ) :
    e6RootParams (ω.foldr e6StarS (fun i => Units.map Fr.toMonoidHom (c (l10mp2a_perm i)))) =
      weylTuple ((coxeterSystem Tag.E6).wordProd ω)
        (fun i => Units.map Fr.toMonoidHom (e6RootParams c (l10mp2a_perm i))) := by
  rw [l10mp2a_cartan_foldr, l10mp2a_cartan_sigma]

theorem l10mp2a_torus_eq {L : Type} [Field L]
    [IsAlgClosed L] (Fr : L →+* L) (v : WeylGroup TwistTag.E6.tag) :
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
        (twistHom TwistTag.E6 L Fr) =
      (l10mp2a_AFix Fr v).map (rootDiagUnitHom TwistTag.E6.tag L) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hx).1
    refine Subgroup.mem_map.2 ⟨a, ?_, rfl⟩
    have hx2 := (mem_twistedTorusOf.1 hx).2
    change canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = rootDiagUnit TwistTag.E6.tag a
      at hx2
    rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit] at hx2
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective hx2
  · rintro ⟨a, ha, rfl⟩
    refine mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
    change canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag a) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = rootDiagUnit TwistTag.E6.tag a
    rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit]
    exact congrArg (rootDiagUnit TwistTag.E6.tag) ha

theorem l10mp2a_image_le {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank)) :
    (twE6Pfix Fr ω).map twE6Cartan ≤ l10mp2a_AFix Fr ((coxeterSystem Tag.E6).wordProd ω) := by
  rintro a ⟨c, hc, rfl⟩
  have hfix : twE6Fp Fr ω c = c := hc
  have hfix' : ω.foldr e6StarS (fun i => Units.map Fr.toMonoidHom (c (l10mp2a_perm i))) = c := by
    change twE6Fp Fr ω c = c
    exact hfix
  have h := l10mp2a_cartan_fp Fr ω c
  change weylTuple ((coxeterSystem Tag.E6).wordProd ω)
      (fun i => Units.map Fr.toMonoidHom (e6RootParams c (l10mp2a_perm i))) = e6RootParams c
  rw [← h, hfix']

end CFSG.StandardType.TwE6Tori

end
