module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20TrA
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem20T

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_autOn_le (hLV : L ≤ Subgroup.normalizer (V : Set G)) {X : Type*} [Group X]
    [Finite X] (φ : ↥L →* X) (hφs : Function.Surjective φ)
    (hk : φ.ker ≤ (Subgroup.centralizer (V : Set G)).subgroupOf L) :
    Nat.card (autOn L V) ≤ Nat.card X := by
  set α : ↥L →* MulAut ↥V := A4.actionOn V L hLV with hα
  have hk' : φ.ker ≤ α.ker := by
    intro k hk1
    rw [MonoidHom.mem_ker, hα, A4.actionOn_eq_one_iff]
    exact Subgroup.mem_subgroupOf.mp (hk hk1)
  set ψ : X →* MulAut ↥V := φ.liftOfSurjective hφs ⟨α, hk'⟩ with hψ
  have hle : autOn L V ≤ ψ.range := by
    intro a ha
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
    exact ⟨φ l, φ.liftOfRightInverse_comp_apply _ _ ⟨α, hk'⟩ l⟩
  calc Nat.card (autOn L V) ≤ Nat.card ψ.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card X := Nat.card_le_card_of_surjective _ ψ.rangeRestrict_surjective

theorem card_autOn_le_quotient (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card (autOn L V) ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  refine card_autOn_le hLV (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) fun k hk => ?_
  rw [QuotientGroup.ker_mk'] at hk
  rw [Subgroup.mem_subgroupOf]
  apply hO2
  exact ⟨k, hk, rfl⟩

omit [Finite G] in
theorem card_eq_of_realizes {W : Type*} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)}
    (h : D.Realizes H ⊤ ⊥) : Nat.card W = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, -, -, -, -, -, -, -, β, hsurj, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hker u).1 hu))
  rw [← Subgroup.card_top (G := W)]
  exact Nat.card_congr (Equiv.ofBijective β ⟨hinj, hsurj⟩)

omit [Finite G] in
theorem card_le_of_realizes {W : Type*} [CommGroup W] {D : FFModel} [Finite D.Gam]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (h : D.Realizes H U Z) :
    Nat.card H ≤ Nat.card D.Gam := by
  obtain ⟨π, hπ, -⟩ := h
  exact Nat.card_le_card_of_surjective π hπ

theorem le_sup_inf_centralizer (hH : Hyp1223 G T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (htop : autOn L V = ⊤) :
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := le_normalizer_of_hyp1223 hH
  have hSyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo hH.sylow le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hSyl le_sup_left (sup_le Subgroup.le_normalizer hH.normalizes)
  set α : ↥L →* MulAut ↥V := A4.actionOn V L hLV with hα
  have hαs : Function.Surjective α := by
    intro a
    have ha : a ∈ autOn L V := by rw [htop]; trivial
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
    exact ⟨l, rfl⟩
  set P := autOn (T ⊓ L) V with hP
  have hPmap : ((T ⊓ L).subgroupOf L).map α = P := by
    ext a
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (A4.mem_autOn_iff (inf_le_right.trans hLV)).mpr
        ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
    · intro ha
      obtain ⟨⟨s, hs⟩, rfl⟩ := (A4.mem_autOn_iff (inf_le_right.trans hLV)).mp ha
      exact ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hPodd : ¬ 2 ∣ P.index := by
    rw [← hPmap]
    exact fun h => hSL.2.2 (h.trans (Subgroup.index_map_dvd _ hαs))
  set Q := autOn T V with hQ
  have hQ2 : IsPGroup 2 ↥Q := by
    have hT2 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      hH.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm
    exact hT2.map _
  have hPQ : P ≤ Q := A4.autOn_mono inf_le_left
  have hrel : P.relIndex Q = 1 := by
    obtain ⟨k, hk⟩ := hQ2.index (P.subgroupOf Q)
    have h1 := Subgroup.relIndex_mul_index hPQ
    have h2 : P.relIndex Q = 2 ^ k := hk
    rcases k with _ | k
    · simpa using h2
    · exfalso
      apply hPodd
      rw [← h1, h2, pow_succ]
      exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _
  have hQP : Q ≤ P := Subgroup.relIndex_eq_one.mp hrel
  intro t ht
  have htQ : A4.actionOn V T hTV ⟨t, ht⟩ ∈ Q := (A4.mem_autOn_iff hTV).mpr ⟨_, rfl⟩
  obtain ⟨⟨s, hs⟩, hst⟩ := (A4.mem_autOn_iff (inf_le_right.trans hLV)).mp (hQP htQ)
  have hsC : s⁻¹ * t ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) hst
    simp only [A4.actionOn_apply_coe] at h1
    calc v * (s⁻¹ * t) = s⁻¹ * (s * v * s⁻¹) * t := by group
      _ = s⁻¹ * (t * v * t⁻¹) * t := by rw [h1]
      _ = s⁻¹ * t * v := by group
  have e : t = s * (s⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs.2)
    (Subgroup.mem_sup_right ⟨T.mul_mem (T.inv_mem hs.1) ht, hsC⟩)

omit [Finite G] in
theorem card_coreMod_mul_two {n : ℕ} (hn : 1 ≤ n) : Nat.card (G6.coreMod n) * 2 = 2 ^ n := by
  let f : G6.PermMod n →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
      map_one' := by simp
      map_mul' := fun x y => by simp [Finset.sum_add_distrib] }
  have hker : f.ker = G6.coreMod n := by
    ext x
    rw [MonoidHom.mem_ker, G6.mem_coreMod]
    exact ofAdd_eq_one
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c)), ?_⟩
    show Multiplicative.ofAdd
      (∑ i, (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c) : Fin n → ZMod 2) i) = c
    rw [Finset.sum_pi_single']
    simp
  have h := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker] at h
  have h1 : Nat.card (G6.PermMod n) = 2 ^ n := by
    show Nat.card (Fin n → ZMod 2) = 2 ^ n
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  rw [h1, h2] at h
  exact h

omit [Finite G] in
theorem card_altDn_ge {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n ≤ Nat.card (↥(FFModel.altDn n).sec ⧸ (FFModel.altDn n).ker.subgroupOf
      (FFModel.altDn n).sec) * 4 := by
  have : Finite (G6.PermMod n) := inferInstanceAs (Finite (Fin n → ZMod 2))
  have : Finite (FFModel.altDn n).Amb := inferInstanceAs (Finite (Fin n → ZMod 2))
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec)
  have hc := card_coreMod_mul_two hn
  have hk : Nat.card ↥((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≤ 2 := by
    have h1 : Nat.card ↥((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≤
        Nat.card ↥(Subgroup.zpowers (G6.allOnes n)) := by
      calc Nat.card ↥((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec)
          = Nat.card ↥(FFModel.altDn n).ker :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
              (FFModel.altDn n).ker ≤ (FFModel.altDn n).sec)).toEquiv
        _ ≤ _ := Subgroup.card_le_of_le (inf_le_left :
              (FFModel.altDn n).ker ≤ Subgroup.zpowers (G6.allOnes n))
    have h2 : G6.allOnes n ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      show (1 : ZMod 2) + 1 = 0
      decide
    have h3 : Nat.card ↥(Subgroup.zpowers (G6.allOnes n)) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one h2
    exact h1.trans (Nat.le_of_dvd (by norm_num) h3)
  have hsec : Nat.card ↥(FFModel.altDn n).sec = Nat.card (G6.coreMod n) := rfl
  rw [hsec] at h
  calc 2 ^ n = Nat.card (G6.coreMod n) * 2 := hc.symm
    _ = Nat.card (↥(FFModel.altDn n).sec ⧸ (FFModel.altDn n).ker.subgroupOf
          (FFModel.altDn n).sec) *
          Nat.card ↥((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) * 2 := by rw [← h]
    _ ≤ _ := by nlinarith

omit [Finite G] in
theorem card_zornO0 {K : Type} [Field K] [Finite K] :
    Nat.card ↥(zornO0 K) = Nat.card K ^ 7 := by
  let e : ↥(zornO0 K) ≃ K × (Fin 3 → K) × (Fin 3 → K) :=
    { toFun := fun x => ((Multiplicative.toAdd x.1).1, (Multiplicative.toAdd x.1).2.1,
        (Multiplicative.toAdd x.1).2.2.1)
      invFun := fun y => ⟨Multiplicative.ofAdd (y.1, y.2.1, y.2.2, -y.1), by
        show y.1 + -y.1 = 0
        ring⟩
      left_inv := fun x => by
        have hx : (Multiplicative.toAdd x.1).1 + (Multiplicative.toAdd x.1).2.2.2 = 0 := x.2
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        show ((Multiplicative.toAdd x.1).1, (Multiplicative.toAdd x.1).2.1,
          (Multiplicative.toAdd x.1).2.2.1, -(Multiplicative.toAdd x.1).1) =
            Multiplicative.toAdd x.1
        have h2 : -(Multiplicative.toAdd x.1).1 = (Multiplicative.toAdd x.1).2.2.2 := by
          rw [neg_eq_iff_add_eq_zero]
          exact hx
        rw [h2]
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

omit [Finite G] in
theorem card_zornQ_ge {K : Type} [Field K] [Finite K] :
    Nat.card K ^ 7 ≤
      Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) * Nat.card K := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((zornR K).subgroupOf (zornO0 K))
  have hR : Nat.card ↥((zornR K).subgroupOf (zornO0 K)) ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥((zornR K).subgroupOf (zornO0 K)) => (Multiplicative.toAdd (x : ↥(zornO0 K)).1).1)
      fun x y hxy => ?_
    have hx : ((x : ↥(zornO0 K)) : Multiplicative (quasithinZorn K)) ∈ zornR K :=
      Subgroup.mem_subgroupOf.mp x.2
    have hy : ((y : ↥(zornO0 K)) : Multiplicative (quasithinZorn K)) ∈ zornR K :=
      Subgroup.mem_subgroupOf.mp y.2
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    have hxy' : c = d := by
      have := hxy
      simp only at this
      rw [hc, hd] at this
      exact this
    apply Subtype.ext
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [hc, hd, hxy']
  rw [card_zornO0] at h
  calc Nat.card K ^ 7 = Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) *
        Nat.card ↥((zornR K).subgroupOf (zornO0 K)) := h
    _ ≤ _ := Nat.mul_le_mul_left _ hR

end Lem20T

open Lem20T

theorem lem12220Transv_of (h1222 : Stmt12_2_2) : Lem12220Transv := by
  classical
  intro G _ _ T L V hH _ A hA hA4 hle
  have htop := autOn_eq_top h1222 hH hA hA4 hle
  have hC := inf_centralizer_eq_bot h1222 hH hA hle
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, hTV, hred, -⟩, -, -, _, hmod⟩ := hall V hH.irrPlus
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact sq_eq_one_of_hyp1223 hH hred v
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hT := le_sup_inf_centralizer hH hTV htop
  have hcardL : Nat.card (autOn L V) = Nat.card (MulAut ↥V) := by
    rw [htop, Subgroup.card_top]
  obtain ⟨m, hVm⟩ : ∃ m : ℕ, Nat.card ↥V = 2 ^ m := by
    let _ := MulAutTwo.zmod2Module hV2'
    exact ⟨_, MulAutTwo.card_eq_pow_finrank⟩
  have hAut : Nat.card (MulAut ↥V) = ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) :=
    MulAutTwo.card_mulAut hV2' hVm
  rw [hAut] at hcardL
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : (v : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨v.2, Subgroup.mem_subgroupOf.mp hv⟩
    rw [hC, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hpow : ∀ k, Nat.card ↥V = 2 ^ k → m = k := fun k hk =>
    Nat.pow_right_injective le_rfl (hVm.symm.trans hk)
  rcases hmod with ⟨n, hn, -, hnat⟩ | ⟨⟨e⟩, hV16, -⟩ | ⟨⟨e⟩, hV10, -⟩ |
      ⟨n, hn5, hn8, -, hnat⟩ | ⟨hV16, φ, hφs, hφk⟩ | ⟨hLie, hG2⟩ | ⟨-, hZ3, ⟨e⟩, -, hV64, -⟩
  ·
    refine ⟨n, hn, ?_, htop, hnat, hT⟩
    obtain ⟨K, _, _, hK, hR⟩ := hnat
    rw [card_eq_of_realizes hR]
    have e2 : Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤) = Nat.card (Fin n → K) := by
      rw [← Subgroup.index_eq_card, Subgroup.bot_subgroupOf, Subgroup.index_bot,
        Subgroup.card_top]
      exact Nat.card_congr Multiplicative.toAdd
    rw [Nat.card_fun, Nat.card_fin, hK, pow_one] at e2
    exact e2
  ·
    exfalso
    have h1 := card_autOn_le_quotient hLV hO2
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (MulAutTwo.slEquivGL 3).toEquiv,
      Matrix.card_GL_field, ZMod.card, hcardL, hpow 4 hV16] at h1
    exact absurd h1 (by decide)
  ·
    exfalso
    have h1 := card_autOn_le_quotient hLV hO2
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (MulAutTwo.slEquivGL 5).toEquiv,
      Matrix.card_GL_field, ZMod.card, hcardL, hpow 10 hV10] at h1
    exact absurd h1 (by decide)
  ·
    exfalso
    rw [hZ] at hnat
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Finite (FFModel.altDn n).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin n)))
    have h1 : Nat.card (autOn L V) ≤ Nat.card ↥(alternatingGroup (Fin n)) :=
      card_le_of_realizes hnat
    rw [nat_card_alternatingGroup, Nat.card_fin, hcardL] at h1
    have h2 := card_altDn_ge (n := n) (by omega)
    rw [← card_eq_of_realizes hnat, hVm] at h2
    have h3 : 2 ^ m ≤ 2 ^ (n - 1) := by
      have : Finite (FFModel.altDn n).Amb := inferInstanceAs (Finite (Fin n → ZMod 2))
      rw [← hVm, card_eq_of_realizes hnat]
      calc Nat.card (↥(FFModel.altDn n).sec ⧸ (FFModel.altDn n).ker.subgroupOf
            (FFModel.altDn n).sec) ≤ Nat.card ↥(FFModel.altDn n).sec :=
            Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
        _ = 2 ^ (n - 1) := by
          have hc := card_coreMod_mul_two (n := n) (by omega)
          have hsec : Nat.card ↥(FFModel.altDn n).sec = Nat.card (G6.coreMod n) := rfl
          rw [hsec]
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [pow_succ] at hc
          simpa using hc
    have hm1 : m ≤ n - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
    have hm2 : n ≤ m + 2 := by
      have : 2 ^ n ≤ 2 ^ (m + 2) := by rw [pow_add]; simpa using h2
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hcases : (n = 5 ∧ (m = 3 ∨ m = 4)) ∨ (n = 6 ∧ (m = 4 ∨ m = 5)) ∨
        (n = 7 ∧ (m = 5 ∨ m = 6)) ∨ (n = 8 ∧ (m = 6 ∨ m = 7)) := by omega
    rcases hcases with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ |
        ⟨rfl, rfl | rfl⟩ <;> exact absurd h1 (by decide)
  ·
    exfalso
    have h1 := card_autOn_le hLV φ hφs (le_of_eq hφk)
    rw [nat_card_alternatingGroup, Nat.card_fin, hcardL, hpow 4 hV16] at h1
    exact absurd h1 (by decide)
  ·
    exfalso
    have h1 : Nat.card (autOn L V) ≤ 339655680 := by
      have h2 := card_autOn_le_quotient hLV hO2
      rcases hLie with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [Nat.card_congr e.toEquiv] at h2
        have : Fintype K := Fintype.ofFinite K
        have h3 : Nat.card (StatedProj (StatedSU 3 (3 ^ 1) K)) ≤ Nat.card (GL (Fin 3) K) :=
          (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective).trans
            (Subgroup.card_le_card_group _)
        have hq : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
        rw [Matrix.card_GL_field, hq] at h3
        exact h2.trans (h3.trans (by decide))
      all_goals exact absurd h0 (by norm_num)
    rw [hcardL] at h1
    rw [hZ] at hG2
    obtain ⟨K, _, _, hK, hR⟩ := hG2
    have h6 : Nat.card ↥V = Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) :=
      card_eq_of_realizes hR
    have h4 := card_zornQ_ge (K := K)
    rw [← h6, hK, hVm] at h4
    have h5 : 2 ^ m ≤ 2 ^ 7 := by
      rw [← hVm, h6]
      calc Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) ≤ Nat.card ↥(zornO0 K) :=
            Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
        _ = 2 ^ 7 := by rw [card_zornO0, hK]; norm_num
    have hm1 : m ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
    have hm2 : 6 ≤ m := by
      by_contra hlt
      have h7 : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h4 h7
      omega
    interval_cases m <;> exact absurd h1 (by decide)
  ·
    exfalso
    have h1 := card_autOn_le_quotient hLV hO2
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, hZ3, nat_card_alternatingGroup, Nat.card_fin] at h3
    rw [h3, hcardL, hpow 6 hV64] at h1
    exact absurd h1 (by decide)

end CFSG.Quasithin.H13
