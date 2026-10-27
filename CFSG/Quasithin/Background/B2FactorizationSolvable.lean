module

public import CFSG.Quasithin.Background.B2FactorizationBlocks
public import CFSG.Quasithin.Background.B2FactorizationBaumannVar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

section Ambient

variable [Finite G] {V H T : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem isPGroup_autI {K : Subgroup G} (hK : IsPGroup 2 K)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) : IsPGroup 2 (autI hV K) :=
  (hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm).map (convI hV)

theorem isSylowTwoOf_autI (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf (autI hV T) (autI hV H) := by
  refine ⟨autI_mono hV hT.1, isPGroup_autI hV hT.2.1 (hT.1.trans hHN), ?_⟩
  have e1 := card_autI_mul_card_inf hV hHN
  have e2 := card_autI_mul_card_inf hV (hT.1.trans hHN)
  have e3 := Subgroup.relIndex_mul_card (autI hV T) (autI hV H)
  rw [inf_eq_left.2 (autI_mono hV hT.1)] at e3
  have e4 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer (V : Set G))
    (H ⊓ Subgroup.centralizer (V : Set G))
  rw [inf_eq_left.2 (inf_le_inf_right _ hT.1)] at e4
  have e5 := Subgroup.relIndex_mul_card T H
  rw [inf_eq_left.2 hT.1] at e5
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have key : T.relIndex H = (autI hV T).relIndex (autI hV H) *
      (T ⊓ Subgroup.centralizer (V : Set G)).relIndex (H ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hTpos ?_
    calc T.relIndex H * Nat.card T = Nat.card H := e5
      _ = Nat.card (autI hV H) * Nat.card ↥(H ⊓ Subgroup.centralizer (V : Set G)) := e1.symm
      _ = ((autI hV T).relIndex (autI hV H) * Nat.card (autI hV T)) *
          ((T ⊓ Subgroup.centralizer (V : Set G)).relIndex
            (H ⊓ Subgroup.centralizer (V : Set G)) *
            Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G))) := by rw [e3, e4]
      _ = ((autI hV T).relIndex (autI hV H) *
          (T ⊓ Subgroup.centralizer (V : Set G)).relIndex
            (H ⊓ Subgroup.centralizer (V : Set G))) *
          (Nat.card (autI hV T) * Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G))) := by ring
      _ = _ * Nat.card T := by rw [e2]
  show ¬ 2 ∣ (autI hV T).relIndex (autI hV H)
  intro h
  apply hT.2.2
  show 2 ∣ T.relIndex H
  rw [key]
  exact Dvd.dvd.mul_right h _

theorem offenderImages_le_autI_thompsonJ (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T H) {B : Subgroup (MulAut (IntMod V hV))} (hB : B ∈ offenderImages hV H)
    (hBT : B ≤ autI hV T) : B ≤ autI hV (thompsonJ T) := by
  obtain ⟨A, hA, rfl⟩ := hB
  have hAH : A ≤ H := hA.1.1
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAH.trans hHN
  set T₁ := preI hV H hHN (autI hV T) with hT₁
  have hT₁H : T₁ ≤ H := preI_le hV
  have hT₁N : T₁ ≤ Subgroup.normalizer (V : Set G) := hT₁H.trans hHN
  have hT₁star : autI hV T₁ = autI hV T := autI_preI hV (autI_mono hV hT.1)
  have hTT₁ : T ≤ T₁ := fun t ht =>
    (mem_preI hV).2 ⟨hT.1 ht, convI_mem_autI hV ht (hTN ht)⟩
  have hAT₁ : A ≤ T₁ := fun a ha =>
    (mem_preI hV).2 ⟨hAH ha, hBT (convI_mem_autI hV ha (hAN ha))⟩
  have hCT₁ : T₁ ⊓ Subgroup.centralizer (V : Set G) = H ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_antisymm (inf_le_inf_right _ hT₁H) fun x hx => ⟨?_, hx.2⟩
    exact inf_centralizer_le_preI hV hx
  have hsylC : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      (H ⊓ Subgroup.centralizer (V : Set G)) := by
    have hSN : T ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      hT.1.trans (le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hHN))
    have h := not_two_dvd_relIndex_inf_of_normalizer (S := T) (D := H ⊓ Subgroup.centralizer (V : Set G))
      (K := H) hT.1 inf_le_left hT.2.2 hSN
    have heq : T ⊓ (H ⊓ Subgroup.centralizer (V : Set G)) = T ⊓ Subgroup.centralizer (V : Set G) :=
      le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩) (fun x hx => ⟨hx.1, hT.1 hx.1, hx.2⟩)
    rw [heq] at h
    exact ⟨inf_le_inf_right _ hT.1, hT.2.1.to_le inf_le_left, h⟩
  have hsyl : IsSylowTwoOf T T₁ := by
    refine isSylowTwoOf_of_isSylowTwoOf_autI hV hT₁N hTT₁ hT.2.1 ?_ ?_
    · rw [hCT₁]
      exact hsylC
    · rw [hT₁star]
      exact ⟨le_rfl, isPGroup_autI hV hT.2.1 hTN, by simp⟩
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_isSylowTwoOf hsyl hAT₁
    (isPGroup_of_isElemAbelian hA.1.2.1)
  have hyH : y ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer (hT₁H hy)
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := hT₁N hy
  have hA'H : IsMaxElemAbelian H (cjSub y A) := isMaxElemAbelian_cjSub hyH hA.1
  have hA'T : IsMaxElemAbelian T (cjSub y A) :=
    ⟨hyA, isElemAbelian_cjSub hA.1.2.1, fun B hBT hBe => hA'H.2.2 B (hBT.trans hT.1) hBe⟩
  have hA'J : cjSub y A ≤ thompsonJ T := le_iSup₂_of_le _ hA'T le_rfl
  have h1 : (autI hV A).map (MulAut.conj (convI hV ⟨y, hyN⟩)).toMonoidHom ≤
      autI hV (thompsonJ T) := by
    rw [autI_cjSub hV hyN A]
    exact autI_mono hV hA'J
  have hy' : convI hV ⟨y, hyN⟩ ∈ autI hV T := hT₁star ▸ convI_mem_autI hV hy hyN
  obtain ⟨t, htT, hty⟩ := (mem_autI hV).1 hy'
  have htN : (t : G) ∈ Subgroup.normalizer (V : Set G) := t.2
  have h2 : (autI hV (thompsonJ T)).map (MulAut.conj (convI hV t)).toMonoidHom =
      autI hV (thompsonJ T) := by
    have := autI_cjSub hV htN (thompsonJ T)
    rw [show (⟨(t : G), htN⟩ : Subgroup.normalizer (V : Set G)) = t from rfl] at this
    rw [this, cjSub_eq_of_mem_normalizer
      (normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer htT))]
  rw [← hty] at h1
  have h3 : (autI hV A).map (MulAut.conj (convI hV t)).toMonoidHom ≤
      (autI hV (thompsonJ T)).map (MulAut.conj (convI hV t)).toMonoidHom := by
    rw [h2]
    exact h1
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (convI hV t)).injective).1 h3

theorem isSylowTwoOf_of_card {M : Type*} [Group M] [Finite M] {A N : Subgroup M} (hAN : A ≤ N)
    (hA : IsPGroup 2 A) {n : ℕ} (hN : Nat.card N = 6 ^ n) (hA' : 2 ^ n ≤ Nat.card A) :
    IsSylowTwoOf A N := by
  refine ⟨hAN, hA, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  have h6 : (6 : ℕ) ^ n = 2 ^ n * 3 ^ n := by
    rw [← mul_pow]
    norm_num
  have hdvd : Nat.card A ∣ Nat.card N := Subgroup.card_dvd_of_le hAN
  rw [hk, hN, h6] at hdvd
  have hcop : Nat.Coprime (2 ^ k) (3 ^ n) := Nat.Coprime.pow k n (by norm_num)
  have hkn : 2 ^ k ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right hdvd
  have hle : 2 ^ k ≤ 2 ^ n := Nat.le_of_dvd (by positivity) hkn
  have hAeq : Nat.card A = 2 ^ n := le_antisymm (hk ▸ hle) hA'
  have h := Subgroup.relIndex_mul_card A N
  rw [inf_eq_left.2 hAN, hAeq, hN, h6] at h
  have hri : A.relIndex N = 3 ^ n :=
    Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) (by rw [h]; ring)
  show ¬ 2 ∣ A.relIndex N
  rw [hri]
  exact fun h2 => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega

end Ambient

section Blocks

variable {W : Type*} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

omit [Finite W] in
theorem _root_.CFSG.Quasithin.IsTransvectionBlocks.card_biSup_eq_prod
    (hb : IsTransvectionBlocks J 𝓗) (S : Subgroup (MulAut W) → Subgroup (MulAut W))
    (hS : ∀ L ∈ 𝓗, S L ≤ L) (s : Finset (Subgroup (MulAut W))) (hs : s ⊆ 𝓗) :
    Nat.card ↥(⨆ L ∈ s, S L) = ∏ L ∈ s, Nat.card ↥(S L) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have haH : a ∈ 𝓗 := hs (Finset.mem_insert_self a s)
    have ih' := ih ((Finset.subset_insert a s).trans hs)
    rw [Finset.iSup_insert, Finset.prod_insert ha, ← ih']
    have hle : (⨆ L ∈ s, S L) ≤
        Subgroup.centralizer ((S a : Subgroup (MulAut W)) : Set (MulAut W)) := by
      refine iSup₂_le fun L hL y hy => ?_
      have hLa : L ≠ a := fun h => ha (h ▸ hL)
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      exact hb.comm a haH L (hs (Finset.mem_insert_of_mem hL)) (Ne.symm hLa) x (hS a haH hx) y
        (hS L (hs (Finset.mem_insert_of_mem hL)) hy)
    have hcomm : ∀ x ∈ S a, ∀ y ∈ (⨆ L ∈ s, S L), x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (hle hy) x hx
    have hinf : S a ⊓ (⨆ L ∈ s, S L) = ⊥ := by
      have hle2 : (⨆ L ∈ s, S L) ≤ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ a), H' := by
        refine iSup₂_le fun L hL => ?_
        have hLa : L ≠ a := fun h => ha (h ▸ hL)
        exact (hS L (hs (Finset.mem_insert_of_mem hL))).trans
          (le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) =>
            ⨆ (_ : H' ≠ a), H') L (hs (Finset.mem_insert_of_mem hL))
            (le_iSup (fun _ : L ≠ a => L) hLa))
      refine le_bot_iff.1 ?_
      calc S a ⊓ (⨆ L ∈ s, S L) ≤ a ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ a), H' :=
            inf_le_inf (hS a haH) hle2
        _ = ⊥ := hb.inf_biSup_ne_eq_bot haH
    have h := card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h

end Blocks

section Struct

variable [Finite G] {V H T : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem isSolvable_autI (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hsolv : Group.IsSolvable ↥H) : Group.IsSolvable ↥(autI hV H) := by
  have h : Group.IsSolvable ↥((convHom hV H hHN).range) :=
    Group.isSolvable_of_surjective (f := (convHom hV H hHN).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rwa [range_convHom] at h

omit [Finite G] in
theorem eq_bot_of_normal_isPGroup (hred : IsTwoReducedIn H V)
    {Q : Subgroup (MulAut (IntMod V hV))} (hQ : Q ≤ autI hV H)
    (hQn : (Q.subgroupOf (autI hV H)).Normal) (hQ2 : IsPGroup 2 Q) : Q = ⊥ := by
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  set D := preI hV H hHN Q with hD
  have hDH : D ≤ H := preI_le hV
  have hDN' : D ≤ Subgroup.normalizer (V : Set G) := hDH.trans hHN
  have hconjQ : ∀ x' ∈ autI hV H, ∀ q ∈ Q, x' * q * x'⁻¹ ∈ Q := fun x' hx' q hq => by
    have := hQn.conj_mem ⟨q, hQ hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨x', hx'⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have hDnorm : H ≤ Subgroup.normalizer (D : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ h ∈ H, ∀ x ∈ D, h * x * h⁻¹ ∈ D := by
      intro h hh x hx
      obtain ⟨hxH, hxQ⟩ := (mem_preI hV).1 hx
      refine (mem_preI hV).2 ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
      have h1 := hconjQ (convI hV ⟨h, hHN hh⟩) (convI_mem_autI hV hh (hHN hh)) _ hxQ
      have h2 : convHom hV H hHN ⟨h * x * h⁻¹, H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)⟩ =
          convHom hV H hHN ⟨h, hh⟩ * convHom hV H hHN ⟨x, hxH⟩ * (convHom hV H hHN ⟨h, hh⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h2]
      exact h1
    intro x
    refine ⟨key h hh x, fun hx => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  have hDpow : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨hdH, hdQ⟩ := (mem_preI hV).1 hd
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hdQ⟩
    refine ⟨k, (convI_eq_one_iff hV ⟨d ^ 2 ^ k, Subgroup.pow_mem _ (hHN hdH) _⟩).1 ?_⟩
    have hk' := congrArg Subtype.val hk
    have h3 : convI hV ⟨d ^ 2 ^ k, Subgroup.pow_mem _ (hHN hdH) _⟩ =
        (convHom hV H hHN ⟨d, hdH⟩) ^ 2 ^ k := by
      rw [← map_pow]
      rfl
    rw [h3]
    simpa [map_pow] using hk'
  have hDC := hred.2.2.2 D hDH hDnorm hDpow
  have : autI hV D = Q := autI_preI hV hQ
  rw [← this]
  exact autI_eq_bot_of_le_centralizer hV hDC

end Struct

section Main

variable [Finite G] {V H T : Subgroup G} (hV : IsElemAbelian 2 V)

theorem structure_of_not_le (hred : IsTwoReducedIn H V) (hsolv : Group.IsSolvable ↥H)
    (hT : IsSylowTwoOf T H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ I : Finset (Subgroup (MulAut (IntMod V hV))),
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
      autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
      (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
      (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
      (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
      fixV (autI hV (thompsonJ H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
      fixV (autI hV (thompsonJ H)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
      (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) ∧
      (∀ g ∈ autI hV H, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
        (commV L).map g.toMonoidHom = commV (B1.conjAut g L)) := by
  have hVH : V ≤ H := hred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
  obtain ⟨-, hstable, hNeq, -⟩ := B2_7_of_not_le hV hVH hHN hJH
  have hsolvX := isSolvable_autI hV hHN hsolv
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 => eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hJX := B1.closure_transvectionsIn_le (autI hV H)
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn (autI hV H))) :=
    B1.solvable_of_le hJX hsolvX
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn (autI hV H)))) =
      Subgroup.closure (transvectionsIn (autI hV H)) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hW hsolvJ hOJ hcl
  obtain ⟨I, hI𝓗, hJPeq, hsylI, -⟩ := hb.stable_decomposition hW hsolvX hO2 hstable
  have hN : autI hV (thompsonJ H) = ⨆ L ∈ I, L := hNeq.trans hJPeq
  have hNnorm : ∀ g ∈ autI hV H, B1.conjAut g (autI hV (thompsonJ H)) = autI hV (thompsonJ H) := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hg
    have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := y.2
    rw [conjAut_eq_map, autI_cjSub hV hyN (thompsonJ H),
      cjSub_eq_of_mem_normalizer (normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hy))]
  have hdec := hb.decomp hW I hI𝓗
  refine ⟨I, ?_, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hTs := isSylowTwoOf_autI hV hHN hT
    have hNX : autI hV (thompsonJ H) ≤ autI hV H := autI_mono hV (thompsonJ_le_self H)
    have hTsN : autI hV T ≤ Subgroup.normalizer
        ((autI hV (thompsonJ H) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
      intro t ht
      refine Subgroup.mem_normalizer_iff''.2 fun x => ?_
      rw [← B1.mem_conjAut, hNnorm t (autI_mono hV hT.1 ht)]
    have hTN : IsSylowTwoOf (autI hV T ⊓ autI hV (thompsonJ H)) (autI hV (thompsonJ H)) :=
      ⟨inf_le_right, (isPGroup_autI hV hT.2.1 (hT.1.trans hHN)).to_le inf_le_left,
        not_two_dvd_relIndex_inf_of_normalizer hTs.1 hNX hTs.2.2 hTsN⟩
    have hLN : ∀ L ∈ I, autI hV (thompsonJ H) ≤
        Subgroup.normalizer ((L : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
      intro L hL
      rw [hN]
      refine iSup₂_le fun L' hL' => ?_
      by_cases hLL : L' = L
      · rw [hLL]
        exact Subgroup.le_normalizer
      · refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((L : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))))
        intro a ha
        exact Subgroup.mem_centralizer_iff.2 fun b hb' =>
          (hb.comm L' (hI𝓗 hL') L (hI𝓗 hL) hLL a ha b hb').symm
    have hLleN : ∀ L ∈ I, L ≤ autI hV (thompsonJ H) := fun L hL => by
      rw [hN]
      exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ I) => K) L hL
        le_rfl
    have hSL : ∀ L ∈ I, IsSylowTwoOf (autI hV T ⊓ L) L := by
      intro L hL
      have h := not_two_dvd_relIndex_inf_of_normalizer
        (S := autI hV T ⊓ autI hV (thompsonJ H)) (D := L) (K := autI hV (thompsonJ H)) hTN.1
        (hLleN L hL) hTN.2.2 (inf_le_right.trans (hLN L hL))
      have heq : (autI hV T ⊓ autI hV (thompsonJ H)) ⊓ L = autI hV T ⊓ L := by
        rw [inf_assoc, inf_eq_right.2 (hLleN L hL)]
      rw [heq] at h
      exact ⟨inf_le_right, (isPGroup_autI hV hT.2.1 (hT.1.trans hHN)).to_le inf_le_left, h⟩
    have hcard2 : ∀ L ∈ I, Nat.card ↥(autI hV T ⊓ L) = 2 := by
      intro L hL
      have h := Subgroup.relIndex_mul_card (autI hV T ⊓ L) L
      rw [inf_eq_left.2 (inf_le_right : autI hV T ⊓ L ≤ L), hb.card_eq L (hI𝓗 hL)] at h
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hSL L hL).2.1
      have hodd : ¬ 2 ∣ (autI hV T ⊓ L).relIndex L := (hSL L hL).2.2
      rw [hk] at h ⊢
      rcases k with _ | _ | k
      · exfalso
        apply hodd
        have : (autI hV T ⊓ L).relIndex L = 6 := by simpa using h
        rw [this]
        norm_num
      · norm_num
      · exfalso
        have h4 : 4 * ((autI hV T ⊓ L).relIndex L * 2 ^ k) = 6 := by
          rw [← h]
          ring
        omega
    have hJt2 : IsPGroup 2 (autI hV (thompsonJ T)) :=
      isPGroup_autI hV (hT.2.1.to_le (thompsonJ_le_self T))
        ((thompsonJ_le_self T).trans (hT.1.trans hHN))
    have hJtN : autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
      autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
    have hScard : Nat.card ↥(⨆ L ∈ I, (autI hV T ⊓ L)) = 2 ^ I.card := by
      have h := hb.card_biSup_eq_prod (fun L => autI hV T ⊓ L) (fun L _ => inf_le_right) I hI𝓗
      beta_reduce at h
      rw [h, Finset.prod_congr rfl hcard2]
      simp
    have hNcard : Nat.card ↥(autI hV (thompsonJ H)) = 6 ^ I.card := by
      have h := hb.card_biSup_eq_prod (fun L => L) (fun L _ => le_rfl) I hI𝓗
      beta_reduce at h
      rw [hN, h, Finset.prod_congr rfl (fun L hL => hb.card_eq L (hI𝓗 hL))]
      simp
    have hSle : (⨆ L ∈ I, (autI hV T ⊓ L)) ≤ autI hV (thompsonJ T) := by
      refine iSup₂_le fun L hL => ?_
      exact offenderImages_le_autI_thompsonJ hV hHN hT (hsylI L hL _ (hSL L hL)) inf_le_left
    exact isSylowTwoOf_of_card hJtN hJt2 hNcard (hScard ▸ Subgroup.card_le_of_le hSle)
  · exact fun L hL L' hL' hne a ha b hb' => hb.comm L (hI𝓗 hL) L' (hI𝓗 hL') hne a ha b hb'
  · intro L hL
    refine le_bot_iff.1 ?_
    calc L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' ≤ L ⊓ ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), L' :=
          inf_le_inf_left L (iSup₂_mono' fun L' hL' => ⟨L', hI𝓗 hL', le_rfl⟩)
      _ = ⊥ := hb.inf_biSup_ne_eq_bot (hI𝓗 hL)
  · intro L hL
    rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hW (hb.card_comm L (hI𝓗 hL)) (hb.le_stabSub (hI𝓗 hL))
      (hb.inf_centSub (hI𝓗 hL)) (hb.autSub_eq_top L (hI𝓗 hL))
  · rw [hN]
    simp only [commV_eq_commSub]
    exact hdec.1
  · rw [hN]
    simp only [commV_eq_commSub]
    exact hdec.2
  · intro L hL
    simp only [commV_eq_commSub]
    refine le_bot_iff.1 ?_
    calc commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' ≤
        commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' :=
          inf_le_inf_left _ (iSup₂_mono' fun L' hL' => ⟨L', hI𝓗 hL', le_rfl⟩)
      _ = ⊥ := hb.commSub_inf_biSup_ne_eq_bot hW (hI𝓗 hL)
  · intro g hg L hL
    have hN' : B1.conjAut g (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, L := by
      rw [← hN, hNnorm g hg]
    refine ⟨hb.conjAut_mem hW hI𝓗 hg hN' hL, ?_⟩
    simp only [commV_eq_commSub]
    exact IsTransvectionBlocks.map_commSub_conjAut L g

theorem isStrongFFStarOffender_mono {W : Type*} [CommGroup W] {X Y A : Subgroup (MulAut W)}
    (hXY : X ≤ Y) (h : IsStrongFFStarOffender X A) : IsStrongFFStarOffender Y A :=
  ⟨isFFStarOffender_mono hXY h.1, h.2⟩

theorem rank_inf_centralizer (hred : IsTwoReducedIn H V) (hsolv : Group.IsSolvable ↥H)
    (hT : IsSylowTwoOf T H) :
    Open.pRank 2 (T ⊓ Subgroup.centralizer (V : Set G)) = Open.pRank 2 T ∧
      thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ thompsonJ T := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hVH : V ≤ H := hred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVT : V ≤ T := (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  ·
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have hA₀Q : A₀ ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
      le_inf hA₀.1 ((le_iSup₂_of_le A₀ hA₀ le_rfl : A₀ ≤ thompsonJ T).trans hJ)
    refine ⟨pRank_eq_of_isMaxElemAbelian hA₀ hA₀Q inf_le_left, ?_⟩
    refine iSup_le fun D => iSup_le fun hD => ?_
    refine le_iSup₂_of_le D ⟨hD.1.trans inf_le_left, hD.2.1, fun B hBT hBe => ?_⟩ le_rfl
    exact (hA₀.2.2 B hBT hBe).trans (hD.2.2 A₀ hA₀Q hA₀.2.1)
  ·
    have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
      hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
    have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
    obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hVH hHN hJH
    have hsolvX := isSolvable_autI hV hHN hsolv
    have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 =>
      eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
    have hq := (B1_8_3 hW hsolvX hO2 hFF).2
    have hcon : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hJ (iSup_le fun A => iSup_le fun hA => hcon A hA)
    obtain ⟨A, hA, hAC⟩ := hcon
    have hnot : ¬ IsStrongFFOffender hV T A := fun h =>
      hq _ (isStrongFFStarOffender_mono (autI_mono hV hT.1) h.2)
    have heq := B2_8_card_eq hV hVT hTN ⟨hA, hAC⟩ hnot
    have h1 : Nat.card (IntMod V hV) = Nat.card V := rfl
    rw [h1, card_autI_eq hV (hA.1.trans hTN), card_fixV_autI hV (hA.1.trans hTN)] at heq
    obtain ⟨-, hrk, hsub, -⟩ := B24_three hV hVT hA heq
    exact ⟨hrk, iSup_le fun D => iSup_le fun hD => le_iSup₂_of_le D (hsub D hD) le_rfl⟩

end Main

end B2F

open B2F in
theorem B2_16 [Finite G] {H T V : Subgroup G} (hsolv : Group.IsSolvable ↥H) (hF : CharTwo H)
    (hT : IsSylowTwoOf T H) (hV : V = conjClosure (quasithinOmegaOneCenter T) H) :
    ∃ hU : IsElemAbelian 2 V, IsTwoReducedIn H V ∧
      ((thompsonJ T ≤ Subgroup.centralizer (V : Set G) ∧
          ∀ h ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (thompsonJ T : Set G),
            ∃ c ∈ H ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), h = n * c) ∨
        (¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) ∧
          ∃ I : Finset (Subgroup (MulAut (IntMod V hU))),
            IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ H)) ∧
            autI hU (thompsonJ H) = ⨆ L ∈ I, L ∧
            (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
            (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
            (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
            fixV (autI hU (thompsonJ H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
            fixV (autI hU (thompsonJ H)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
            (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) ∧
            (∀ g ∈ autI hU H, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
              (commV L).map g.toMonoidHom = commV (B1.conjAut g L)))) ∧
      Open.pRank 2 (T ⊓ Subgroup.centralizer (V : Set G)) = Open.pRank 2 T ∧
      thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ thompsonJ T := by
  subst hV
  obtain ⟨hU, hcase⟩ := B2_15 hF hT
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  refine ⟨hU, hred, ?_, rank_inf_centralizer hred hsolv hT⟩
  rcases hcase with ⟨hJ, -, -⟩ | ⟨hJ, hfact⟩
  · exact Or.inr ⟨hJ, structure_of_not_le hU hred hsolv hT hJ⟩
  · refine Or.inl ⟨hJ, fun h hh => ?_⟩
    obtain ⟨c, hc, n, hn, hcn⟩ := hfact h⁻¹ (H.inv_mem hh)
    refine ⟨n⁻¹, ⟨H.inv_mem hn.1, (Subgroup.normalizer _).inv_mem hn.2⟩, c⁻¹,
      ⟨H.inv_mem hc.1, (Subgroup.centralizer _).inv_mem hc.2⟩, ?_⟩
    rw [← mul_inv_rev, ← hcn, inv_inv]

end CFSG.Quasithin
