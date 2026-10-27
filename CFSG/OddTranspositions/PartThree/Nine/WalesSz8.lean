module

public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.OddTranspositions.PartThree.Nine.Wales

open CFSG.Quasithin CFSG.ComponentClassification.AschbacherToolkit.Bender
open scoped MatrixGroups

@[expose] def gf8List : List GF8 := (List.finRange 8).map GF8.mk

@[expose] def gf8Triples : List (GF8 × GF8 × GF8) :=
  gf8List.flatMap fun x => gf8List.flatMap fun y => gf8List.map fun z => (x, y, z)

@[expose] def gf8Lin (v : GF8 × GF8 × GF8) (a : GF8) : GF8 :=
  (if a.val.val % 2 = 1 then v.1 else 0) + (if a.val.val / 2 % 2 = 1 then v.2.1 else 0) +
    (if a.val.val / 4 % 2 = 1 then v.2.2 else 0)

@[expose] def gf8Bij : List (GF8 × GF8 × GF8) :=
  gf8Triples.filter fun v =>
    gf8List.all fun a => gf8List.all fun b => a == b || gf8Lin v a != gf8Lin v b

@[expose] def szSylow8SquareCheck : Bool :=
  gf8Bij.all fun v => gf8Bij.all fun w =>
    !(gf8List.all fun a => gf8Lin w (a ^ 5) == gf8Lin v a ^ 5) ||
      gf8List.all fun a => (gf8Lin v)^[21] a == a

theorem szSylow8SquareCheck_eq_true : szSylow8SquareCheck = true := by
  decide +kernel

private theorem mem_gf8List (a : GF8) : a ∈ gf8List :=
  List.mem_map.mpr ⟨a.val, List.mem_finRange _, rfl⟩

private theorem mem_gf8Bij {v : GF8 × GF8 × GF8} (hv : Function.Injective (gf8Lin v)) :
    v ∈ gf8Bij := by
  obtain ⟨x, y, z⟩ := v
  rw [gf8Bij, List.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [gf8Triples, List.mem_flatMap, List.mem_map]
    exact ⟨x, mem_gf8List x, y, mem_gf8List y, z, mem_gf8List z, rfl⟩
  · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    intro a _ b _
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr fun h => hab (hv h)

private theorem iterate_twentyOne_eq {v w : GF8 × GF8 × GF8} (hv : Function.Injective (gf8Lin v))
    (hw : Function.Injective (gf8Lin w)) (hvw : ∀ a, gf8Lin w (a ^ 5) = gf8Lin v a ^ 5)
    (a : GF8) : (gf8Lin v)^[21] a = a := by
  have h := szSylow8SquareCheck_eq_true
  rw [szSylow8SquareCheck, List.all_eq_true] at h
  have h' := h v (mem_gf8Bij hv)
  rw [List.all_eq_true] at h'
  have h'' := h' w (mem_gf8Bij hw)
  have hall : (gf8List.all fun a => gf8Lin w (a ^ 5) == gf8Lin v a ^ 5) = true :=
    List.all_eq_true.mpr fun a _ => beq_iff_eq.mpr (hvw a)
  rw [hall, Bool.not_true, Bool.false_or, List.all_eq_true] at h''
  exact beq_iff_eq.mp (h'' a (mem_gf8List a))

private theorem eq_gf8Lin_of_map_add (f : GF8 → GF8) (hf : ∀ a b, f (a + b) = f a + f b)
    (a : GF8) : f a = gf8Lin (f ⟨1⟩, f ⟨2⟩, f ⟨4⟩) a := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)
  have hsum : a = (if a.val.val % 2 = 1 then (⟨1⟩ : GF8) else 0) +
      (if a.val.val / 2 % 2 = 1 then (⟨2⟩ : GF8) else 0) +
        (if a.val.val / 4 % 2 = 1 then (⟨4⟩ : GF8) else 0) := by
    revert a
    decide
  conv_lhs => rw [hsum]
  rw [hf, hf, gf8Lin]
  split_ifs <;> simp only [h0]

private theorem gf8_add_self (a : GF8) : a + a = 0 := by
  revert a
  decide

private theorem gf8_eq_of_add_eq_zero {a b : GF8} (h : a + b = 0) : a = b := by
  revert h
  revert a b
  decide

private theorem gf8_exists_pow_five (b : GF8) : ∃ a : GF8, a ^ 5 = b := by
  revert b
  decide

theorem iterate_twentyOne_eq_id {al ga : GF8 → GF8} (hal : ∀ a b, al (a + b) = al a + al b)
    (hga : ∀ a b, ga (a + b) = ga a + ga b) (hali : Function.Injective al)
    (hgai : Function.Injective ga) (h : ∀ a, ga (a ^ 5) = al a ^ 5) :
    al^[21] = id ∧ ga^[21] = id := by
  obtain ⟨v, hv⟩ : ∃ v, ∀ a, al a = gf8Lin v a := ⟨_, eq_gf8Lin_of_map_add al hal⟩
  obtain ⟨w, hw⟩ : ∃ w, ∀ a, ga a = gf8Lin w a := ⟨_, eq_gf8Lin_of_map_add ga hga⟩
  have hvi : Function.Injective (gf8Lin v) := fun a b hab => hali (by rw [hv, hv]; exact hab)
  have hwi : Function.Injective (gf8Lin w) := fun a b hab => hgai (by rw [hw, hw]; exact hab)
  have h21 := iterate_twentyOne_eq hvi hwi fun a => by
    rw [← hv, ← hw]
    exact h a
  have hal21 : al^[21] = id := by
    rw [show al = gf8Lin v from funext hv]
    exact funext h21
  refine ⟨hal21, funext fun b => ?_⟩
  have hk : ∀ k a, ga^[k] (a ^ 5) = (al^[k] a) ^ 5 := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h]
  obtain ⟨a, rfl⟩ := gf8_exists_pow_five b
  rw [hk, hal21]
  rfl

theorem conj_pow_twentyOne_eq {G : Type*} [Group G] {T U : Subgroup G} {p q : G → GF8}
    (hp : ∀ s ∈ T, ∀ t ∈ T, p (s * t) = p s + p t) (hps : ∀ a, ∃ t ∈ T, p t = a)
    (hpZ : ∀ t ∈ T, p t = 0 ↔ ∀ s ∈ T, Commute t s)
    (hU : ∀ t ∈ T, t * t ∈ U) (hUsq : ∀ v ∈ U, ∃ t ∈ T, v = t * t)
    (hq : ∀ v ∈ U, ∀ w ∈ U, q (v * w) = q v + q w) (hqi : Set.InjOn q U)
    (hsq : ∀ t ∈ T, q (t * t) = p t ^ 5) {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G))
    {v : G} (hv : v ∈ U) : n ^ 21 * v * (n ^ 21)⁻¹ = v := by
  classical
  have hnT : ∀ t ∈ T, n * t * n⁻¹ ∈ T := fun t ht => (hn t).mp ht
  have hnT' : ∀ t ∈ T, n⁻¹ * t * n ∈ T := fun t ht => by
    simpa using (Subgroup.inv_mem _ hn t).mp ht
  have hp1 : p 1 = 0 := by simpa using hp 1 T.one_mem 1 T.one_mem
  have hpinv : ∀ t ∈ T, p t⁻¹ = p t := fun t ht => by
    have h := hp t ht t⁻¹ (T.inv_mem ht)
    rw [mul_inv_cancel, hp1] at h
    exact (gf8_eq_of_add_eq_zero h.symm).symm
  have hcent : ∀ z ∈ T, (∀ s ∈ T, Commute z s) → ∀ s ∈ T, Commute (n * z * n⁻¹) s := by
    intro z hz hzc s hs
    have h := (Commute.conj_iff n).mpr (hzc _ (hnT' s hs))
    simpa [mul_assoc] using h
  have hcent' : ∀ z ∈ T, (∀ s ∈ T, Commute (n * z * n⁻¹) s) → ∀ s ∈ T, Commute z s := by
    intro z hz hzc s hs
    have h := (Commute.conj_iff n⁻¹).mpr (hzc _ (hnT s hs))
    simpa [mul_assoc] using h
  choose tf htfT htfp using hps
  set al : GF8 → GF8 := fun a => p (n * tf a * n⁻¹) with hal
  have hkey : ∀ t ∈ T, p (n * t * n⁻¹) = al (p t) := by
    intro t ht
    have hz : (tf (p t))⁻¹ * t ∈ T := T.mul_mem (T.inv_mem (htfT _)) ht
    have hpz : p ((tf (p t))⁻¹ * t) = 0 := by
      rw [hp _ (T.inv_mem (htfT _)) _ ht, hpinv _ (htfT _), htfp, gf8_add_self]
    have hzc := hcent _ hz ((hpZ _ hz).mp hpz)
    have hnz : p (n * ((tf (p t))⁻¹ * t) * n⁻¹) = 0 := (hpZ _ (hnT _ hz)).mpr hzc
    have ht' : n * t * n⁻¹ = n * tf (p t) * n⁻¹ * (n * ((tf (p t))⁻¹ * t) * n⁻¹) := by group
    rw [ht', hp _ (hnT _ (htfT _)) _ (hnT _ hz), hnz, add_zero]
  have hal_add : ∀ a b, al (a + b) = al a + al b := by
    intro a b
    have h := hkey _ (T.mul_mem (htfT a) (htfT b))
    rw [hp _ (htfT a) _ (htfT b), htfp, htfp] at h
    rw [← h]
    have h' : n * (tf a * tf b) * n⁻¹ = n * tf a * n⁻¹ * (n * tf b * n⁻¹) := by group
    rw [h', hp _ (hnT _ (htfT a)) _ (hnT _ (htfT b))]
  have hal_inj : Function.Injective al := by
    intro a b hab
    apply gf8_eq_of_add_eq_zero
    have h0 : al (a + b) = 0 := by rw [hal_add, hab, gf8_add_self]
    have h1 := hkey _ (T.mul_mem (htfT a) (htfT b))
    rw [hp _ (htfT a) _ (htfT b), htfp, htfp, h0] at h1
    have h2 := hcent' _ (T.mul_mem (htfT a) (htfT b))
      ((hpZ _ (hnT _ (T.mul_mem (htfT a) (htfT b)))).mp h1)
    have h3 := (hpZ _ (T.mul_mem (htfT a) (htfT b))).mpr h2
    rwa [hp _ (htfT a) _ (htfT b), htfp, htfp] at h3
  have hnU : ∀ w ∈ U, n * w * n⁻¹ ∈ U := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := hUsq w hw
    have h : n * (t * t) * n⁻¹ = n * t * n⁻¹ * (n * t * n⁻¹) := by group
    rw [h]
    exact hU _ (hnT t ht)
  choose fifth hfifth using gf8_exists_pow_five
  set vf : GF8 → G := fun b => tf (fifth b) * tf (fifth b) with hvf
  have hvfU : ∀ b, vf b ∈ U := fun b => hU _ (htfT _)
  have hqvf : ∀ b, q (vf b) = b := fun b => by rw [hvf, hsq _ (htfT _), htfp, hfifth]
  set ga : GF8 → GF8 := fun b => q (n * vf b * n⁻¹) with hga
  have hkey2 : ∀ w ∈ U, q (n * w * n⁻¹) = ga (q w) := by
    intro w hw
    have h : vf (q w) = w := hqi (hvfU _) hw (hqvf _)
    rw [hga]
    simp only
    rw [h]
  have hga_add : ∀ b b', ga (b + b') = ga b + ga b' := by
    intro b b'
    have hU2 : vf b * vf b' ∈ U := U.mul_mem (hvfU b) (hvfU b')
    have h : vf (b + b') = vf b * vf b' :=
      hqi (hvfU _) hU2 (by rw [hqvf, hq _ (hvfU b) _ (hvfU b'), hqvf, hqvf])
    have h' : n * (vf b * vf b') * n⁻¹ = n * vf b * n⁻¹ * (n * vf b' * n⁻¹) := by group
    show q (n * vf (b + b') * n⁻¹) = q (n * vf b * n⁻¹) + q (n * vf b' * n⁻¹)
    rw [h, h', hq _ (hnU _ (hvfU b)) _ (hnU _ (hvfU b'))]
  have hga_inj : Function.Injective ga := by
    intro b b' h
    have h1 : n * vf b * n⁻¹ = n * vf b' * n⁻¹ := hqi (hnU _ (hvfU b)) (hnU _ (hvfU b')) h
    have h2 : vf b = vf b' := by simpa using h1
    rw [← hqvf b, ← hqvf b', h2]
  have hrel : ∀ a, ga (a ^ 5) = al a ^ 5 := by
    intro a
    have h := hkey2 _ (hU _ (htfT a))
    rw [hsq _ (htfT a), htfp] at h
    rw [← h]
    have h' : n * (tf a * tf a) * n⁻¹ = n * tf a * n⁻¹ * (n * tf a * n⁻¹) := by group
    rw [h', hsq _ (hnT _ (htfT a))]
  have hga21 := (iterate_twentyOne_eq_id hal_add hga_add hal_inj hga_inj hrel).2
  have hit : ∀ k : ℕ, ∀ w ∈ U, n ^ k * w * (n ^ k)⁻¹ ∈ U ∧
      q (n ^ k * w * (n ^ k)⁻¹) = ga^[k] (q w) := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      obtain ⟨hk1, hk2⟩ := ih w hw
      have h : n ^ (k + 1) * w * (n ^ (k + 1))⁻¹ = n * (n ^ k * w * (n ^ k)⁻¹) * n⁻¹ := by
        rw [pow_succ']
        group
      rw [h, Function.iterate_succ_apply', ← hk2]
      exact ⟨hnU _ hk1, hkey2 _ hk1⟩
  obtain ⟨h1, h2⟩ := hit 21 v hv
  rw [hga21] at h2
  exact hqi h1 hv h2

private noncomputable def gf8Equiv : GF8 ≃+* GaloisField 2 (2 * 1 + 1) :=
  haveI : Fintype (GaloisField 2 (2 * 1 + 1)) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 (2 * 1 + 1) (by norm_num), Nat.card_eq_fintype_card]
    decide)

private theorem exists_coords_rootSub : ∃ c : GF8 × GF8 ≃ SuzukiAut.rootSub 1,
    ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4) := by
  let f : GF8 × GF8 → SuzukiAut.rootSub 1 := fun p =>
    ⟨SuzukiAut.root 1 (gf8Equiv p.1) (gf8Equiv p.2), SuzukiAut.root_mem 1 _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      obtain ⟨ha, hb⟩ := SuzukiAut.root_injective 1 (congrArg Subtype.val h)
      exact Prod.ext (gf8Equiv.injective ha) (gf8Equiv.injective hb)
    · rintro ⟨g, hg⟩
      obtain ⟨a, b, rfl⟩ := (SuzukiAut.mem_rootSub 1).mp hg
      exact ⟨(gf8Equiv.symm a, gf8Equiv.symm b), by simp [f]⟩
  refine ⟨Equiv.ofBijective f hf, fun a b a' b' => Subtype.ext ?_⟩
  simp only [Equiv.ofBijective_apply, f, Subgroup.coe_mul]
  rw [SuzukiAut.root_mul 1 (by norm_num), SuzukiAut.tits_apply]
  simp [map_add, map_mul, map_pow]

theorem exists_coords_of_sylow (P : Sylow 2 (CFSG.Theory.Comparator.SzModel 1)) :
    ∃ c : GF8 × GF8 ≃ P,
      ∀ a b a' b' : GF8, c (a, b) * c (a', b') = c (a + a', b + b' + a * a' ^ 4) := by
  obtain ⟨c₀, hc₀⟩ := exists_coords_rootSub
  let e₁ := MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1)
  let P₁ := P.mapSurjective (f := e₁.toMonoidHom) e₁.surjective
  obtain ⟨S₀, hS₀⟩ := SuzukiAut.exists_sylow_eq_rootSub 1 (by norm_num)
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) :=
    Finite.of_equiv _ e₁.toEquiv
  have hP₁ := Sylow.coe_mapSurjective (f := e₁.toMonoidHom) e₁.surjective P
  let e : (P : Subgroup (CFSG.Theory.Comparator.SzModel 1)) ≃* SuzukiAut.rootSub 1 :=
    ((Subgroup.equivMapOfInjective _ e₁.toMonoidHom e₁.injective).trans
      (MulEquiv.subgroupCongr hP₁.symm)).trans
      ((Sylow.equiv P₁ S₀).trans (MulEquiv.subgroupCongr hS₀))
  refine ⟨c₀.trans e.symm.toEquiv, fun a b a' b' => ?_⟩
  simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  rw [← map_mul, hc₀]

end CFSG.OddTranspositions.PartThree.Nine.Wales
