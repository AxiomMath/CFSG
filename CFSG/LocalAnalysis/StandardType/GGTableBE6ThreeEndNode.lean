module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCore
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCount
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCoroot
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction.EPilot CFSG.SeitzReduction CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

namespace E6ThreeEnd

section Count

variable {τ : Tag} {K : Type} [Field K]

@[expose] def expE (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (E : Subgroup (ModGL τ K)) :
    AddSubgroup (Fin τ.rank → ZMod 3) where
  carrier := {x | rootDiagUnit τ (zetaVec ζ hζ x) ∈ E}
  add_mem' := fun {x y} hx hy => by
    have e : zetaVec ζ hζ (x + y) = zetaVec ζ hζ x * zetaVec ζ hζ y := by
      funext i
      change zmodPowHom ζ hζ (.ofAdd (x i + y i)) =
        zmodPowHom ζ hζ (.ofAdd (x i)) * zmodPowHom ζ hζ (.ofAdd (y i))
      rw [ofAdd_add, map_mul]
    change rootDiagUnit τ (zetaVec ζ hζ (x + y)) ∈ E
    rw [e, rootDiagUnit_mul]
    exact mul_mem hx hy
  zero_mem' := by
    have e : zetaVec ζ hζ (0 : Fin τ.rank → ZMod 3) = 1 := by
      funext i
      change zmodPowHom ζ hζ (.ofAdd 0) = 1
      rw [ofAdd_zero, map_one]
    change rootDiagUnit τ (zetaVec ζ hζ 0) ∈ E
    rw [e, rootDiagUnit_one]
    exact one_mem E
  neg_mem' := fun {x} hx => by
    have e : zetaVec ζ hζ (-x) = (zetaVec ζ hζ x)⁻¹ := by
      funext i
      change zmodPowHom ζ hζ (.ofAdd (-x i)) = (zmodPowHom ζ hζ (.ofAdd (x i)))⁻¹
      rw [ofAdd_neg]
      exact map_inv (zmodPowHom ζ hζ) (Multiplicative.ofAdd (x i))
    change rootDiagUnit τ (zetaVec ζ hζ (-x)) ∈ E
    rw [e, ← rootDiagUnit_inv]
    exact inv_mem hx

theorem mem_expE {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {E : Subgroup (ModGL τ K)}
    {x : Fin τ.rank → ZMod 3} : x ∈ expE ζ hζ E ↔ rootDiagUnit τ (zetaVec ζ hζ x) ∈ E :=
  Iff.rfl


theorem card_eq_mul_card_expE {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {S : Subgroup (WeylGroup τ)} {E : Subgroup (ModGL τ K)} [Finite E] (hE : IsElemAbelian 3 E)
    (hEX : E ≤ xHat τ K S) :
    ∃ A : Subgroup (WeylGroup τ), A ≤ S ∧ IsElemAbelian 3 A ∧
      (∀ x ∈ expE ζ hζ E, ∀ a ∈ A, adAct τ 3 a x = x) ∧
      Nat.card E = Nat.card A * Nat.card (expE ζ hζ E) := by
  have hEM : E ≤ monoHat τ K := hEX.trans (xHat_le_monoHat S)
  set ψE : E →* WeylGroup τ := (psiHat τ K).comp (Subgroup.inclusion hEM) with hψE
  have hψS : ∀ e : E, ψE e ∈ S := fun e => (mem_xHat.mp (hEX e.2)).2
  have hker : ∀ e : E, ψE e = 1 → ∃ x, (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) := by
    intro e he
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (x := Subgroup.inclusion hEM e) he
    have hb' : (e : ModGL τ K) = rootDiagUnit τ b := hb
    have hbp : b ^ 3 = 1 := by
      have h1 : (e : ModGL τ K) ^ 3 = 1 := hE.2 _ e.2
      rw [hb', rootDiagUnit_pow] at h1
      exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    obtain ⟨x, hx⟩ := exists_zetaVec_eq hζo hζ hbp
    exact ⟨x, by rw [hb', hx]⟩
  have hfix : ∀ (e₀ : E) (e : E) (x : Fin τ.rank → ZMod 3),
      (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) → adAct τ 3 (ψE e₀) x = x := by
    intro e₀ e x hx
    have hc := conj_rootDiagUnit_of_mem_monoHat (Subgroup.inclusion hEM e₀) (zetaVec ζ hζ x)
    have hcomm : (e₀ : ModGL τ K) * e * (e₀ : ModGL τ K)⁻¹ = e := by
      rw [TableB.IsElemAbelian.comm hE e₀.2 e.2, mul_inv_cancel_right]
    rw [weylTuple_zetaVec] at hc
    have h2 : rootDiagUnit τ (zetaVec ζ hζ (adAct τ 3 (ψE e₀) x)) =
        rootDiagUnit τ (zetaVec ζ hζ x) := by
      rw [← hx, ← hcomm, hx]
      exact hc.symm
    exact zetaVec_injective hζo hζ (rootDiagUnit_injective h2)
  refine ⟨ψE.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact hψS e
  · exact isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ψE
  · rintro x hx _ ⟨e₀, rfl⟩
    exact hfix e₀ ⟨_, hx⟩ x rfl
  · have hcardE := TableB.card_range_mul_card_ker ψE
    have hmem : ∀ x : expE ζ hζ E,
        (⟨rootDiagUnit τ (zetaVec ζ hζ x.1), x.2⟩ : E) ∈ ψE.ker := fun x =>
      MonoidHom.mem_ker.mpr (psiHat_eq (mapsRootLines_rootDiagUnit _))
    have hk : Nat.card (expE ζ hζ E) = Nat.card ψE.ker := by
      refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩)
      · intro x y hxy
        have h1 := congrArg (fun z : ψE.ker => ((z : E) : ModGL τ K)) hxy
        exact Subtype.ext (zetaVec_injective hζo hζ (rootDiagUnit_injective h1))
      · rintro ⟨e, he⟩
        obtain ⟨x, hx⟩ := hker e he
        have hxE : x ∈ expE ζ hζ E := by
          rw [mem_expE, ← hx]
          exact e.2
        exact ⟨⟨x, hxE⟩, Subtype.ext (Subtype.ext hx.symm)⟩
    rw [hk]
    exact hcardE.symm

end Count

theorem map_congr_inv_map_conj {R : Type*} [Group R] (g : MulAut R) (X : Subgroup (MulAut R)) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.congr g⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id X
  ext φ x
  simp [MulAut.congr, MulAut.conj_apply]

section Main

variable {K : Type} [Field K]

theorem card_fix_gE6 (i : Fin 3) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adAct .E6 3 (gE6 i) x = x} ≤ 3 ^ (6 - 2) := by
  have e : ∀ x, adAct .E6 3 (gE6 i) x = adWord .E6 3 (wordE6G i) x :=
    fun x => (adWord_eq_adAct _ x).symm
  simp only [e]
  fin_cases i
  · exact card_fix_adWordE6G0
  · exact card_fix_adWordE6G1
  · exact card_fix_adWordE6G2

theorem autEndNode_of_le_hatAut [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card X) : AutEndNode X := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  set κ := hatAut .E6 K with hκ
  set Y : Subgroup (hatGroup .E6 K) := X.comap κ with hY
  set f : Y →* X := (κ.comp Y.subtype).codRestrict X (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hXI hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hXp : IsPGroup 3 (⊤ : Subgroup X) := fun g => by
    obtain ⟨k, hk⟩ := TableB.isPGroup_of_isElemAbelian hX ⟨g.1, g.1.2⟩
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hXp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPX : P.map κ = X := by
    have hcomp : κ.comp Y.subtype = X.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3) hP3
  set P' := P.map (MulAut.conj c).toMonoidHom with hP'
  set E : Subgroup (ModGL .E6 K) := P'.map (hatGroup .E6 K).subtype with hEdef
  have hEX : E ≤ xHat .E6 K modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hc hp)
  have hker : ∀ p ∈ P', κ p = 1 → p = 1 := fun p hp h1 =>
    eq_one_of_hatAut_eq_one (xHat_le_monoHat _ (hEX ⟨p, hp, rfl⟩)) h1
  have hP'X : P'.map κ = X.map (MulAut.conj (κ c)).toMonoidHom := by
    have hcomp : κ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (κ c)).toMonoidHom.comp κ :=
      MonoidHom.ext fun p => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    rw [hP', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPX]
  have hcardP' : Nat.card P' = Nat.card X := by
    rw [← card_map_eq_of_ker κ hker, hP'X,
      Subgroup.card_map_of_injective (MulAut.conj (κ c)).injective]
  have hcardE : Nat.card E = Nat.card X := by
    rw [hEdef, Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective, hcardP']
  have hXc : IsElemAbelian 3 (X.map (MulAut.conj (κ c)).toMonoidHom) :=
    TableB.isElemAbelian_map hX _
  have hP'ab : ∀ p ∈ P', ∀ p' ∈ P', p * p' = p' * p := by
    intro p hp p' hp'
    have h1 : κ (p * p' * (p' * p)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        TableB.IsElemAbelian.comm hXc (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
          (hP'X ▸ ⟨p', hp', rfl⟩ : κ p' ∈ _), mul_inv_cancel]
    have h2 := hker _ (mul_mem (mul_mem hp hp') (inv_mem (mul_mem hp' hp))) h1
    exact mul_inv_eq_one.mp h2
  have hP'3 : ∀ p ∈ P', p ^ 3 = 1 := by
    intro p hp
    refine hker _ (pow_mem hp 3) ?_
    rw [map_pow]
    exact hXc.2 _ (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
  have hP'el : IsElemAbelian 3 P' :=
    ⟨⟨⟨fun a b => Subtype.ext (hP'ab a a.2 b b.2)⟩⟩, hP'3⟩
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map hP'el _
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have : Finite E := Finite.of_surjective (fun p : P' => (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : E))
    (by rintro ⟨_, ⟨p, hp, rfl⟩⟩; exact ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨A, hAS, hA, hAfix, hcount⟩ := card_eq_mul_card_expE hζo hζ hE hEX
  have hE5 : 3 ^ 5 ≤ Nat.card E := hcardE ▸ h5
  have hcor : ∃ (a : Fin Tag.E6.rank → ZMod 3) (ω : List (Fin Tag.E6.rank)),
      a ∈ expE ζ hζ E ∧ adWord .E6 3 ω a = Pi.single (highNode .E6) 1 := by
    by_cases hA1 : A = ⊥
    · have hXE : 3 ^ (Tag.E6.rank - 1) ≤ Nat.card (expE ζ hζ E) := by
        rw [hcount, hA1, Subgroup.card_bot, one_mul] at hE5
        exact hE5
      obtain ⟨cc, hcc⟩ := exists_forall_mem_iff_dot (expE ζ hζ E) hXE
      obtain ⟨k, hk⟩ := exists_cover cc
      exact ⟨coverVec k, coverWord k, (hcc _).mpr hk, adWord_coverWord k⟩
    · rcases refined_E6 A hAS hA hA1 with hlt | ⟨i, hi⟩
      · exfalso
        have hle : Nat.card (expE ζ hζ E) ≤
            Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x} :=
          Nat.card_le_card_of_injective (fun x => ⟨x.1, hAfix x.1 x.2⟩)
            fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
        have hlt' : Nat.card E < 3 ^ 5 := by
          rw [hcount]
          exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hle) hlt
        exact absurd hE5 (not_le.mpr hlt')
      ·
        refine ⟨gVec i, gWord i, ?_, adWord_gWord i⟩
        have hg1 : gE6 i ≠ 1 := by
          intro h
          apply hA1
          rw [hi, h, Subgroup.zpowers_one_eq_bot]
        have hcardA : Nat.card A = 3 := by
          rw [hi, Nat.card_zpowers, orderOf_eq_prime (gE6_pow_three i) hg1]
        have hXE4 : 3 ^ (6 - 2) ≤ Nat.card (expE ζ hζ E) := by
          rw [hcount, hcardA] at hE5
          have h' : 3 * 3 ^ (6 - 2) ≤ 3 * Nat.card (expE ζ hζ E) := hE5
          exact Nat.le_of_mul_le_mul_left h' (by norm_num)
        have hgA : gE6 i ∈ A := by
          rw [hi]
          exact Subgroup.mem_zpowers _
        let ι : expE ζ hζ E → {x : Fin Tag.E6.rank → ZMod 3 // adAct .E6 3 (gE6 i) x = x} :=
          fun x => ⟨x.1, hAfix x.1 x.2 _ hgA⟩
        have hι : Function.Injective ι := fun a b hab =>
          Subtype.ext (by simpa [ι] using congrArg Subtype.val hab)
        have hιs : Function.Surjective ι :=
          ((Nat.bijective_iff_injective_and_card ι).mpr
            ⟨hι, le_antisymm (Nat.card_le_card_of_injective ι hι)
              ((card_fix_gE6 i).trans hXE4)⟩).2
        have hgF : adAct .E6 3 (gE6 i) (gVec i) = gVec i :=
          (adWord_eq_adAct (wordE6G i) (gVec i)).symm.trans (adWord_wordE6G_gVec i)
        obtain ⟨⟨x, hx⟩, hxg⟩ := hιs ⟨gVec i, hgF⟩
        have hxe : x = gVec i := congrArg Subtype.val hxg
        rw [← hxe]
        exact hx
  obtain ⟨a, ω, haE, haω⟩ := hcor
  obtain ⟨hsurj, -⟩ := TableBExc.weylQuotientHom_surjective_ker (τ := .E6) (K := K)
  obtain ⟨⟨n, hn⟩, hnω⟩ := hsurj ((coxeterSystem .E6).wordProd ω)
  have hconj : n * rootDiagUnit .E6 (zetaVec ζ hζ a) * n⁻¹ =
      rootDiagUnit .E6 (highDiag .E6 ζ) := by
    have hmaps : MapsRootLines n ((coxeterSystem .E6).wordProd ω) := by
      rw [← hnω]
      exact mapsRootLines_weylQuotientHom ⟨n, hn⟩
    rw [monomial_conj_rootDiagUnit_weylTuple hn hmaps, weylTuple_zetaVec, ← adWord_eq_adAct, haω]
    congr 1
    funext j
    rw [zetaVec_apply, highDiag]
    by_cases hj : j = highNode .E6
    · rw [hj, Pi.single_eq_same, Pi.mulSingle_eq_same, ZMod.val_one, pow_one]
    · rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, ZMod.val_zero, pow_zero]
  set nh : hatGroup .E6 K := ⟨n, monoHat_le_hatGroup (monomial_le_monoHat hn)⟩ with hnh
  set P'' := P'.map (MulAut.conj nh).toMonoidHom with hP''
  have hP''m : ∀ x ∈ P'', (x : ModGL .E6 K) ∈ monoHat .E6 K := by
    rintro _ ⟨y, hy, rfl⟩
    have hym : (y : ModGL .E6 K) ∈ monoHat .E6 K := xHat_le_monoHat _ (hEX ⟨y, hy, rfl⟩)
    have hnm : n ∈ monoHat .E6 K := monomial_le_monoHat hn
    exact mul_mem (mul_mem hnm hym) (inv_mem hnm)
  have hP''3 : ∀ x ∈ P'', x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hP'3 y hy, map_one]
  have ht : endNodeHat ζ ∈ P'' := by
    obtain ⟨y, hy, hyd⟩ := mem_expE.mp haE
    have hyd' : (y : ModGL .E6 K) = rootDiagUnit .E6 (zetaVec ζ hζ a) := hyd
    refine ⟨y, hy, Subtype.ext ?_⟩
    change n * (y : ModGL .E6 K) * n⁻¹ = rootDiagUnit .E6 (highDiag .E6 ζ)
    rw [hyd']
    exact hconj
  have hcore := autEndNode_of_le_monoHat hζo hP''3 hP''m ht
  have hcomp2 : (MulAut.conj (κ nh)).toMonoidHom.comp (MulAut.conj (κ c)).toMonoidHom =
      (MulAut.conj (κ (nh * c))).toMonoidHom := MonoidHom.ext fun φ => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, MulAut.mul_apply]
  have hcompn : κ.comp (MulAut.conj nh).toMonoidHom = (MulAut.conj (κ nh)).toMonoidHom.comp κ :=
    MonoidHom.ext fun p => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
  have hmapX : P''.map κ = X.map (MulAut.conj (κ (nh * c))).toMonoidHom := by
    rw [hP'', Subgroup.map_map, hcompn, ← Subgroup.map_map, hP'X, Subgroup.map_map, hcomp2]
  rw [hmapX] at hcore
  have h := hcore.map (κ (nh * c))⁻¹
  rwa [map_congr_inv_map_conj] at h

end Main

end E6ThreeEnd

end CFSG.StandardType
