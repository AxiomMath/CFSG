module

public import CFSG.Quasithin.H13.L32A770l
public import CFSG.Quasithin.H13.L32A770k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem gen_not_mem_u0 (h : Hyp147 G T L V) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h68 : Lemma14_7_68) {zα : G} (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V))
    (hzα1 : zα ≠ 1) : zα ∉ u0 T V := by
  intro hm
  apply N.zα_not_le_u0 hF h68 h
  intro w hw
  rcases eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1 w hw with rfl | rfl
  · exact one_mem _
  · exact hm

omit N in
theorem mem_normalizer_E (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {z zα n : G}
    (hz0 : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V))
    (hzα1 : zα ≠ 1) (hnz : n * z * n⁻¹ ∈ fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V))
    (hnzα : n * zα * n⁻¹ ∈ fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V)) :
    n ∈ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) := by
  have hgen := eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1
  have hgenα := eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1
  rw [← conjSub_eq_self_iff]
  refine conjSub_eq_of_le ?_
  rw [conjSub_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    show n * w * n⁻¹ ∈ _
    rcases hgen w hw with rfl | rfl
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
    · exact hnz
  · rintro _ ⟨w, hw, rfl⟩
    show n * w * n⁻¹ ∈ _
    rcases hgenα w hw with rfl | rfl
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
    · exact hnzα

theorem normalizer_inf_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h68 : Lemma14_7_68)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) :
    hz T V ⊓ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  have hzαu := N.gen_not_mem_u0 h hF h68 hzα hzα1
  have hzu : z ∈ u0 T V := fsuV1_le_u0 h hMod hz0
  have hne : zα ≠ z := fun e => hzαu (e ▸ hzu)
  have hgenα := eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1
  have hcE := N.isPGroup_cE h hMod h63 hF h1222 h1332 h1334 h68 h2
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hzαU := hZU hzα
  have hzU : z ∈ fsuU T V := centralizerMod_le_left _ _ _ hzu
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hzz : z * z = 1 := by rw [← sq]; exact hUe z hzU
  have hTH : T ≤ hz T V := hF.T_le_H
  have hP : IsPGroup 2 ↥(hz T V ⊓ Subgroup.normalizer (E : Set G)) := by
    intro n
    have hnH : (n : G) ∈ hz T V := (Subgroup.mem_inf.mp n.2).1
    have hnE : (n : G) ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.mp n.2).2
    have hnz : (n : G) * z * (n : G)⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hnH z hz0
      rw [← this, mul_inv_cancel_right]
    have hn1 := (Subgroup.mem_normalizer_iff.mp hnE zα).mp (Subgroup.mem_sup_right hzα)
    have hsq : (n : G) * n * zα * ((n : G) * n)⁻¹ = zα := by
      rcases N.mem_E h hMod h63 hF h1222 h1332 h1334 h2 hz0 hz1 hzα hzα1 _ hn1 with
        e | e | e | e
      · exfalso; apply hzα1
        calc zα = (n : G)⁻¹ * ((n : G) * zα * (n : G)⁻¹) * n := by group
          _ = 1 := by rw [e]; group
      · exfalso; apply hne
        calc zα = (n : G)⁻¹ * ((n : G) * zα * (n : G)⁻¹) * n := by group
          _ = (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * n := by rw [e, hnz]
          _ = z := by group
      · calc (n : G) * n * zα * ((n : G) * n)⁻¹ =
            (n : G) * ((n : G) * zα * (n : G)⁻¹) * (n : G)⁻¹ := by group
          _ = zα := by rw [e, e]
      · calc (n : G) * n * zα * ((n : G) * n)⁻¹ =
            (n : G) * ((n : G) * zα * (n : G)⁻¹) * (n : G)⁻¹ := by group
          _ = (n : G) * (z * zα) * (n : G)⁻¹ := by rw [e]
          _ = ((n : G) * z * (n : G)⁻¹) * ((n : G) * zα * (n : G)⁻¹) := by group
          _ = z * (z * zα) := by rw [hnz, e]
          _ = zα := by rw [← mul_assoc, hzz, one_mul]
    have hn2C : (n : G) * n ∈ hz T V ⊓
        Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) := by
      refine ⟨mul_mem hnH hnH, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      rcases hgenα w hw with rfl | rfl
      · group
      · calc w * ((n : G) * n) = (n : G) * n * w * ((n : G) * n)⁻¹ * ((n : G) * n) := by rw [hsq]
          _ = (n : G) * n * w := by group
    obtain ⟨m, hm⟩ := hcE ⟨_, hn2C⟩
    refine ⟨m + 1, Subtype.ext ?_⟩
    have h1 : ((n : G) * n) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h2 : (n : G) ^ 2 ^ (m + 1) = 1 := by
      rw [pow_succ', pow_mul, sq]
      exact h1
    simpa using h2
  refine le_antisymm ?_ (le_inf hTH hTE)
  refine le_of_isPGroup_of_le_normalizer h hP fun t ht => ?_
  rw [← conjSub_eq_self_iff, conjSub_inf, conjSub_eq_self_iff.mpr
    (Subgroup.le_normalizer (hTH ht)), ← conjSub_normalizer, conjSub_eq_self_iff.mpr (hTE ht)]

theorem relIndex_T_X (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) :
    T.relIndex (Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) = 3 := by
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  set X := Subgroup.normalizer (E : Set G) with hX
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  have hzαu := N.gen_not_mem_u0 h hF h68 hzα hzα1
  have hzu : z ∈ u0 T V := fsuV1_le_u0 h hMod hz0
  have hne : zα ≠ z := fun e => hzαu (e ▸ hzu)
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hzU : z ∈ fsuU T V := centralizerMod_le_left _ _ _ hzu
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hzz : z * z = 1 := by rw [← sq]; exact hUe z hzU
  have hcom : z * zα = zα * z := hUc z hzU zα (hZU hzα)
  have hNHE := N.normalizer_inf_eq h hMod h63 hF h1222 h1332 h1334 h68 h2 hTE
  obtain ⟨q, hqQ, hqzα⟩ := N.exists_q h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2 hz0 hz1
    hzα hzα1
  obtain ⟨a, haQ, haz⟩ := N.exists_a h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hz0 hz1
    hzα hzα1
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hqQ
  have hqz : q * z * q⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hqH z hz0
    rw [← this, mul_inv_cancel_right]
  have haα : a * zα * a⁻¹ = zα := by
    have haG : a ∈ conjSub ((k : G) * g) (hz T V) := conjSub_mono _ (pCoreOf_le 2 _) haQ
    rw [← conjSub_centralizer] at haG
    have := Subgroup.mem_centralizer_iff.mp haG zα hzα
    rw [← this, mul_inv_cancel_right]
  have hzE : z ∈ E := Subgroup.mem_sup_left hz0
  have hzαE : zα ∈ E := Subgroup.mem_sup_right hzα
  have hzzαE : z * zα ∈ E := mul_mem hzE hzαE
  have hqX : q ∈ X := mem_normalizer_E (g := g) (k := k) hF hz0 hz1 hzα hzα1 (by rw [hqz]; exact hzE)
    (by rw [hqzα]; exact hzzαE)
  have haX : a ∈ X := mem_normalizer_E (g := g) (k := k) hF hz0 hz1 hzα hzα1
    (by rw [haz, ← hcom]; exact hzzαE) (by rw [haα]; exact hzαE)
  let _ : MulAction ↥X G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp X.subtype)
  have hsmul : ∀ (x : ↥X) (w : G), x • w = (x : G) * w * (x : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥X z = T.subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxH : (x : G) ∈ hz T V := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        rcases eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1 v hv with rfl | rfl
        · group
        · calc v * (x : G) = (x : G) * v * (x : G)⁻¹ * x := by rw [hx]
            _ = (x : G) * v := by group
      rw [← hNHE]
      exact ⟨hxH, x.2⟩
    · intro hx
      have := Subgroup.mem_centralizer_iff.mp (hF.T_le_H hx) z hz0
      rw [← this, mul_inv_cancel_right]
  have horb : MulAction.orbit ↥X z = {z, zα, z * zα} := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      show (x : G) * z * (x : G)⁻¹ ∈ _
      have h1 : (x : G) * z * (x : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp x.2 z).mp hzE
      rcases N.mem_E h hMod h63 hF h1222 h1332 h1334 h2 hz0 hz1 hzα hzα1 _ h1 with
        e | e | e | e
      · exfalso; apply hz1
        calc z = (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * x := by group
          _ = 1 := by rw [e]; group
      · rw [e]; exact Or.inl rfl
      · rw [e]; exact Or.inr (Or.inl rfl)
      · rw [e]; exact Or.inr (Or.inr rfl)
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw <;> rw [hw]
      · exact MulAction.mem_orbit_self _
      · refine ⟨⟨q⁻¹ * a, mul_mem (inv_mem hqX) haX⟩, ?_⟩
        have hqc : q * z = z * q := by
          calc q * z = q * z * q⁻¹ * q := by group
            _ = z * q := by rw [hqz]
        have hqz' : q⁻¹ * z * q = z := by rw [mul_assoc, ← hqc]; group
        have hqα' : q⁻¹ * zα * q = z * zα := by
          calc q⁻¹ * zα * q = q⁻¹ * (z * (z * zα)) * q := by
                rw [show z * (z * zα) = zα by rw [← mul_assoc, hzz, one_mul]]
            _ = q⁻¹ * (z * (q * zα * q⁻¹)) * q := by rw [hqzα]
            _ = (q⁻¹ * z * q) * zα := by group
            _ = z * zα := by rw [hqz']
        show (q⁻¹ * a) * z * (q⁻¹ * a)⁻¹ = zα
        calc (q⁻¹ * a) * z * (q⁻¹ * a)⁻¹ = q⁻¹ * (a * z * a⁻¹) * q := by group
          _ = q⁻¹ * (zα * z) * q := by rw [haz]
          _ = (q⁻¹ * zα * q) * (q⁻¹ * z * q) := by group
          _ = z * zα * z := by rw [hqα', hqz']
          _ = zα := by rw [mul_assoc, ← hcom, ← mul_assoc, hzz, one_mul]
      · refine ⟨⟨a, haX⟩, ?_⟩
        show a * z * a⁻¹ = z * zα
        rw [haz, hcom]
  have hidx := MulAction.index_stabilizer ↥X z
  rw [hstab, horb] at hidx
  rw [Subgroup.relIndex, hidx]
  refine Set.ncard_eq_three.mpr ⟨z, zα, z * zα, hne.symm, ?_, ?_, rfl⟩
  · intro e
    apply hzα1
    calc zα = z⁻¹ * (z * zα) := by group
      _ = 1 := by rw [← e]; group
  · intro e
    apply hz1
    calc z = z * zα * zα⁻¹ := by group
      _ = 1 := by rw [← e]; group

theorem comm_zα_of_normal (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G))
    {P : Subgroup G} (hPT : P ≤ T)
    (hPN : conjSub ((k : G) * g) (pCoreOf 2 (hz T V)) ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) := by
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  have hzαu := N.gen_not_mem_u0 h hF h68 hzα hzα1
  have hzu : z ∈ u0 T V := fsuV1_le_u0 h hMod hz0
  have hne : zα ≠ z := fun e => hzαu (e ▸ hzu)
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hzU : z ∈ fsuU T V := centralizerMod_le_left _ _ _ hzu
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hzz : z * z = 1 := by rw [← sq]; exact hUe z hzU
  have hcom : z * zα = zα * z := hUc z hzU zα (hZU hzα)
  have hgenα := eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1
  obtain ⟨a, haQ, haz⟩ := N.exists_a h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hz0 hz1
    hzα hzα1
  have haα : a⁻¹ * zα * a = zα := by
    have haG : a ∈ conjSub ((k : G) * g) (hz T V) := conjSub_mono _ (pCoreOf_le 2 _) haQ
    rw [← conjSub_centralizer] at haG
    have := Subgroup.mem_centralizer_iff.mp haG zα hzα
    calc a⁻¹ * zα * a = a⁻¹ * (zα * a) := by group
      _ = a⁻¹ * (a * zα) := by rw [this]
      _ = zα := by group
  have hTz : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hF.T_le_H ht) z hz0
    rw [← this, mul_inv_cancel_right]
  have hfix : ∀ p ∈ P, p * zα * p⁻¹ = zα := by
    intro p hp
    have hpT := hPT hp
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTE hpT) zα).mp (Subgroup.mem_sup_right hzα)
    rcases N.mem_E h hMod h63 hF h1222 h1332 h1334 h2 hz0 hz1 hzα hzα1 _ h1 with
      e | e | e | e
    · exfalso; apply hzα1
      calc zα = p⁻¹ * (p * zα * p⁻¹) * p := by group
        _ = 1 := by rw [e]; group
    · exfalso; apply hne
      calc zα = p⁻¹ * (p * zα * p⁻¹) * p := by group
        _ = p⁻¹ * (p * z * p⁻¹) * p := by rw [e, hTz p hpT]
        _ = z := by group
    · exact e
    · exfalso
      have hp' : a⁻¹ * p * a ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hPN haQ)) p).mp hp
        simpa using this
      have h2' := hTz _ (hPT hp')
      apply hne
      calc zα = a⁻¹ * zα * a := haα.symm
        _ = a⁻¹ * ((z * zα) * z) * a := by
            rw [show (z * zα) * z = zα by rw [mul_assoc, ← hcom, ← mul_assoc, hzz, one_mul]]
        _ = a⁻¹ * ((p * zα * p⁻¹) * (p * z * p⁻¹)) * a := by rw [e, hTz p hpT]
        _ = a⁻¹ * (p * (zα * z) * p⁻¹) * a := by group
        _ = a⁻¹ * (p * (a * z * a⁻¹) * p⁻¹) * a := by rw [haz]
        _ = (a⁻¹ * p * a) * z * (a⁻¹ * p * a)⁻¹ := by group
        _ = z := h2'
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rcases hgenα w hw with rfl | rfl
  · group
  · calc w * p = p * w * p⁻¹ * p := by rw [hfix p hp]
      _ = p * w := by group

theorem Qα_le_normalizer_E (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    conjSub ((k : G) * g) (pCoreOf 2 (hz T V)) ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) := by
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  have hzW : z ∈ conjSub ((k : G) * g) (fsuU T V) :=
    N.F_le_Uα h hMod hF h2 (N.v1_le h hMod h63 hF h1222 h1332 h1334 h69 h2 hz0)
  intro c hc
  refine mem_normalizer_E (g := g) (k := k) hF hz0 hz1 hzα hzα1 ?_ ?_
  · rw [show c * z * c⁻¹ = (c * z * c⁻¹ * z⁻¹) * z by group]
    exact mul_mem (Subgroup.mem_sup_right (comm_mem_zα h hMod hF hc hzW))
      (Subgroup.mem_sup_left hz0)
  · have hcG : c ∈ conjSub ((k : G) * g) (hz T V) := conjSub_mono _ (pCoreOf_le 2 _) hc
    rw [← conjSub_centralizer] at hcG
    have := Subgroup.mem_centralizer_iff.mp hcG zα hzα
    rw [← this, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right hzα

theorem card_T_ge (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8) :
    2 ^ 11 ≤ Nat.card ↥T := by
  have hU := card_U_eq h hMod h63 h8
  have hUQ : fsuU T V ≤ pCoreOf 2 (hz T V) := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf
  have hQT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le h hF.T_le_H
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have he := N.commutator_zα_eq h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2
  have hne : (fsuU T V).relIndex (pCoreOf 2 (hz T V)) ≠ 1 := by
    intro h1
    have hQU : pCoreOf 2 (hz T V) ≤ fsuU T V := Subgroup.relIndex_eq_one.mp h1
    have hb : ⁅conjSub ((k : G) * g) (fsuV1 T V), pCoreOf 2 (hz T V)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw q hq
      rw [Subgroup.mem_bot, commutatorElement_def, fsuU_comm h (hZU hw) (hQU hq),
        mul_inv_cancel_right, mul_inv_cancel]
    rw [he] at hb
    have := hF.card_V₁
    rw [hb, Subgroup.card_bot] at this
    omega
  have h1 := Subgroup.relIndex_mul_card (fsuU T V) (pCoreOf 2 (hz T V))
  rw [inf_eq_left.mpr hUQ, hU] at h1
  have hpos : (fsuU T V).relIndex (pCoreOf 2 (hz T V)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have h2' := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) T
  rw [inf_eq_left.mpr hQT, relIndex_QH_T h h63 hF] at h2'
  have hQ : 2 ^ 8 ≤ Nat.card ↥(pCoreOf 2 (hz T V)) := by
    rw [← h1]
    have : 2 ≤ (fsuU T V).relIndex (pCoreOf 2 (hz T V)) := by omega
    calc 2 ^ 8 = 2 * 2 ^ 7 := by norm_num
      _ ≤ (fsuU T V).relIndex (pCoreOf 2 (hz T V)) * 2 ^ 7 := Nat.mul_le_mul_right _ this
  rw [← h2']
  calc 2 ^ 11 = 8 * 2 ^ 8 := by norm_num
    _ ≤ 8 * Nat.card ↥(pCoreOf 2 (hz T V)) := Nat.mul_le_mul_left _ hQ

theorem exists_normal (hedge : GoldschmidtEdgeBoundSubgroups.{0}) (h : Hyp147 G T L V)
    (hMod : StmtL32NModule) (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) :
    ∃ N₀ : Subgroup G, N₀ ≠ ⊥ ∧ N₀ ≤ T ∧
      (L₁Of L (fsuV1 T V) ⊔ T) ⊔ Subgroup.normalizer
        ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) ≤
          Subgroup.normalizer (N₀ : Set G) ∧
      N₀ ≤ Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) ∧
      N₀ ≤ Subgroup.centralizer (V : Set G) := by
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  set X := Subgroup.normalizer (E : Set G) with hX
  have hNHE := N.normalizer_inf_eq h hMod h63 hF h1222 h1332 h1334 h68 h2 hTE
  have hC : (L₁Of L (fsuV1 T V) ⊔ T) ⊓ X = T := by
    refine le_antisymm ?_ (le_inf le_sup_right hTE)
    exact (inf_le_inf_right _ hF.L₁T_le_H).trans hNHE.le
  have hcard : 2 ^ 7 < Nat.card ↥T := by
    have := N.card_T_ge h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2 h8
    omega
  obtain ⟨N₀, hN₀1, hN₀T, hN₀N⟩ := exists_normal_of_edgeBound hedge hC
    (relIndex_T_L1T h hMod h63 hF h1222 h1332 h1334)
    (N.relIndex_T_X h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hTE) hcard
  have hQαX := N.Qα_le_normalizer_E h hMod h63 hF h1222 h1332 h1334 h69 h2
  have hcZ := N.comm_zα_of_normal h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hTE hN₀T
    (hQαX.trans (le_sup_right.trans hN₀N))
  refine ⟨N₀, hN₀1, hN₀T, hN₀N, hcZ, ?_⟩
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hzαVU : zα ∈ V ⊔ u0 T V := by
    rw [← N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ]
    exact Subgroup.mem_sup_left (N.zα_le h hMod h63 hF h1222 h1332 h1334 h2 hzα)
  exact le_centralizer_V h hMod hF h1222 h1332 h1334 (hN₀T.trans hF.T_le_H)
    (le_sup_left.trans hN₀N) hzαVU (N.gen_not_mem_u0 h hF h68 hzα hzα1)
    fun p hp => (Subgroup.mem_centralizer_iff.mp (hcZ hp) zα hzα).symm

end Not1471

end CFSG.Quasithin.H13.L32A
