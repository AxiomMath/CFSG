module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptK
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF2b
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptYO2Abs
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptYO2Wr
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptYO2Y
public import CFSG.Quasithin.Vol2.Ch3Sec3NFOuter

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.GorensteinWalter
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.Lem3313B CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem yo2_mk_one_iff {H₀ : Subgroup G} (x : ↥H₀) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) x = 1 ↔ (x : G) ∈ pCoreOf 2 H₀ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy

theorem yo2_card_le_two_mul {T S : Subgroup G} {t' : G} (ht' : t' ∈ T)
    (h : ∀ s ∈ T, s ∈ S ∨ t'⁻¹ * s ∈ S) : Nat.card T ≤ 2 * Nat.card ↥(T ⊓ S) := by
  set N := (T ⊓ S).subgroupOf T with hN
  have hmul : Nat.card N * N.index = Nat.card T := Subgroup.card_mul_index N
  have hcardN : Nat.card N = Nat.card ↥(T ⊓ S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ S ≤ T)).toEquiv
  have hidx : N.index ≤ 2 := by
    let f : Bool → T ⧸ N := fun b => if b then ((1 : T) : T ⧸ N) else ((⟨t', ht'⟩ : T) : T ⧸ N)
    have hsurj : Function.Surjective f := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H s =>
        rcases h s s.2 with hs | hs
        · refine ⟨true, ?_⟩
          show ((1 : T) : T ⧸ N) = (s : T ⧸ N)
          rw [QuotientGroup.eq]
          simp only [inv_one, one_mul]
          exact ⟨s.2, hs⟩
        · refine ⟨false, ?_⟩
          show ((⟨t', ht'⟩ : T) : T ⧸ N) = (s : T ⧸ N)
          rw [QuotientGroup.eq]
          exact ⟨T.mul_mem (T.inv_mem ht') s.2, hs⟩
    have h1 := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
    exact h1
  calc Nat.card T = Nat.card N * N.index := hmul.symm
    _ ≤ Nat.card N * 2 := Nat.mul_le_mul_left _ hidx
    _ = 2 * Nat.card ↥(T ⊓ S) := by rw [hcardN]; ring

theorem leafYO2_holds (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) :
    LeafYO2 := by
  intro G _ _ T M L D H K c hin
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := c.hyp.simple
  obtain ⟨t', ht'T, ht'n, hK'c, hKK', hKK, hTsw⟩ := c.exists_pair h37 h38
  set K' := K.map (MulAut.conj t').toMonoidHom with hK'
  set H₀ := H ⊔ D with hH₀
  have hTH : T ≤ H := c.inH.1
  have hHH₀ : H ≤ H₀ := le_sup_left
  have hTH₀ : T ≤ H₀ := hTH.trans hHH₀
  have hT2 : IsPGroup 2 T := c.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, hT2, Vol2.Ch10.SecA.not_two_dvd_index_of_le c.hyp.sylow hTH⟩
  have hT₀ : IsSylowTwoOf T H₀ := c.isSylowTwoOf_H₀
  have hHtop : pCoreOf 2 H ≠ ⊥ := c.inH.2
  obtain ⟨e⟩ := c.wreath
  obtain ⟨q, hq, hq24, hmod⟩ := c.model
  have hq5 : 5 ≤ q := by omega
  have h3 : q % 8 = 3 ∨ q % 8 = 5 := by omega
  have : Fact q.Prime := ⟨hq⟩
  have hF : Nat.card (GaloisField q 1) = q := by
    rw [GaloisField.card q 1 (by norm_num), pow_one]
  obtain ⟨P3, hP3Y, hP3c, hP3e, hYRP⟩ := yo2_Y_split hTsyl hHtop e
  set Y := oTwoUpper H with hY
  set R := pCoreOf 2 Y with hR
  have hYH : Y ≤ H := oTwoUpper_le H
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hKH₀ : K ≤ H₀ := le_of_mem_cComp c.K_comp
  have hK'H₀ : K' ≤ H₀ := le_of_mem_cComp hK'c
  have hYK : Y ≤ K ⊔ K' := hKK ▸ c.YK
  have hK₀H₀ : K ⊔ K' ≤ H₀ := sup_le hKH₀ hK'H₀
  have hKcl : LocalSQTK G := (qtkeCore_of_cat c.hyp.nonabelian c.hyp.qtke).1
  have hHN : H₀ ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKcl h37 h38 c.O hT₀ c.K_comp
    rwa [hKK] at this
  have hKN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp c.K_comp hK'c)
  have hKo : pCoreOf 2 K ≤ pCoreOf 2 H₀ :=
    f2_pCoreOf_le_sandwich le_sup_left hKN hK₀H₀ hHN
  set π : ↥H₀ →* ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) with hπ
  set A := modO2Image H₀ K with hA
  set A' := modO2Image H₀ K' with hA'
  have ht'H₀ : t' ∈ H₀ := hTH₀ ht'T
  set σ : H₀ ⧸ CFSG.pCore 2 ↥H₀ := π ⟨t', ht'H₀⟩ with hσ
  have hA'eq : A' = A.map (MulAut.conj σ).toMonoidHom := modO2Image_conj ⟨t', ht'H₀⟩
  obtain ⟨e₁⟩ := modO2_mulEquiv c.K_comp
  obtain ⟨e₂⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2 q 1 hmod
  let eA : ↥A ≃* PSL2 (GaloisField q 1) := e₁.symm.trans e₂
  let eA' : ↥A' ≃* PSL2 (GaloisField q 1) :=
    (MulEquiv.subgroupCongr hA'eq).trans
      ((Subgroup.equivMapOfInjective A (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective).symm.trans
        eA)
  have hcomm_KK' := Vol2Native.lemma_1_2_1_two hKcl h37 c.O c.K_comp hK'c hKK'
  have hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hx' : (x : G) ∈ K := hx
    have hy' : (y : G) ∈ K' := hy
    have h1 : ⁅(x : G), (y : G)⁆ ∈ pCoreOf 2 H₀ :=
      hcomm_KK'.2 (hcomm_KK'.1 (Subgroup.commutator_mem_commutator hx' hy'))
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) (x * y * x⁻¹ * y⁻¹) = 1 :=
      (yo2_mk_one_iff (x * y * x⁻¹ * y⁻¹)).mpr (by simpa [commutatorElement_def] using h1)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
      _ = π y * π x := by rw [h2, one_mul]
  have hi : A ⊓ A' = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have hk1 : k = 1 :=
      yo2_center_trivial hF hq hq5 eA hk.1 (fun a ha => (hc a ha k hk.2).symm)
    rw [hk1]
    exact Subgroup.one_mem _
  set Yb := modO2Image H₀ Y with hYb_def
  set Rb := modO2Image H₀ R with hRb_def
  set Pb := modO2Image H₀ P3 with hPb_def
  have hYb : Yb ≤ A ⊔ A' := by
    have h1 : modO2Image H₀ Y ≤ modO2Image H₀ (K ⊔ K') := img_mono hYK
    rw [img_sup hKH₀ hK'H₀] at h1
    exact h1
  have hRYb : Rb ≤ Yb := img_mono hRY
  have hYN : Y ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hRN : ∀ y ∈ Yb, ∀ r ∈ Rb, y * r * y⁻¹ ∈ Rb := fun y hy r hr =>
    (Subgroup.mem_normalizer_iff.mp (img_le_normalizer hYN hy) r).mp hr
  have hRH₀ : R ≤ H₀ := hRY.trans (hYH.trans hHH₀)
  have hR2G : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hR2 : IsPGroup 2 Rb := (hR2G.of_equiv (Subgroup.subgroupOfEquivOfLe hRH₀).symm).map π
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3H₀ : P3 ≤ H₀ := hP3Y.trans (hYH.trans hHH₀)
  have hP3pg : IsPGroup 3 P3 := IsPGroup.of_card (n := 2) (by rw [hP3c]; norm_num)
  have hPY : Pb ≤ Yb := img_mono hP3Y
  have hP9 : Nat.card Pb = 9 := by
    have hd := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 (pCoreOf 2 H₀) hP3pg
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀)
    rw [yo2_img_card hP3H₀ hd.eq_bot, hP3c]
  have hP3' : ∀ y ∈ Pb, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hP3e x hx)
    rw [← map_pow, this, map_one]
  have hYRP' : ∀ y ∈ Yb, ∃ r ∈ Rb, ∃ p ∈ Pb, y = r * p := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, p, hp, hrp⟩ := hYRP (x : G) hx
    have hrH : r ∈ H₀ := hRH₀ hr
    have hpH : p ∈ H₀ := hP3H₀ hp
    refine ⟨π ⟨r, hrH⟩, mk_mem_img _ hr, π ⟨p, hpH⟩, mk_mem_img _ hp, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hrp
  have hRN' : H ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y (le_normalizer_oTwoUpper H hx)
  have hTbN : ∀ t (ht : t ∈ H₀), t ∈ H → π ⟨t, ht⟩ ∈ Subgroup.normalizer (Rb : Set _) := by
    intro t ht htH
    have h1 : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) :=
      (Subgroup.zpowers_le).mpr (hRN' htH)
    exact img_le_normalizer h1 (mk_mem_img ⟨t, ht⟩ (Subgroup.mem_zpowers t))
  have hσR : ∀ r, r ∈ Rb ↔ σ * r * σ⁻¹ ∈ Rb :=
    Subgroup.mem_normalizer_iff.mp (hTbN t' ht'H₀ (hTH ht'T))
  have hσA : ∀ a, a ∈ A ↔ σ * a * σ⁻¹ ∈ A' := by
    intro a
    rw [hA'eq, A38.mem_map_conj]
    simp [mul_assoc]
  have hdich := yo2_abstract hF hq hq5 h3 eA eA' hc hi hYb hRYb hRN hR2 hPY hP9 hP3' hYRP' hσR hσA
  have hker : ∀ u v : ↥H₀, ((u : G) * (v : G)⁻¹) ∈ pCoreOf 2 H₀ → π u = π v := by
    intro u v huv
    have h1 : π (u * v⁻¹) = 1 := (yo2_mk_one_iff (u * v⁻¹)).mpr huv
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  rcases hdich with hgood | hbad
  ·
    rw [hKK, Subgroup.commutator_le]
    intro r hr y hy
    have hrY : r ∈ Y := hRY hr
    have hrH₀ : r ∈ H₀ := hRH₀ hr
    have hyH₀ : y ∈ H₀ := hHH₀ (hYH hy)
    have hcomm : π ⟨r, hrH₀⟩ * π ⟨y, hyH₀⟩ = π ⟨y, hyH₀⟩ * π ⟨r, hrH₀⟩ :=
      hgood _ (mk_mem_img _ hr) _ (mk_mem_img _ hy)
    have hcomm1 : ⁅r, y⁆ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem hrY hy) (Y.inv_mem hrY)) (Y.inv_mem hy)
    have h1 : π (⟨r, hrH₀⟩ * ⟨y, hyH₀⟩ * ⟨r, hrH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 : ⁅r, y⁆ ∈ pCoreOf 2 H₀ :=
      (yo2_mk_one_iff (⟨r, hrH₀⟩ * ⟨y, hyH₀⟩ * ⟨r, hrH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹)).mp h1
    exact inf_pCoreOf_le hK₀H₀ ⟨hYK hcomm1, h2⟩
  ·
    exfalso
    have hRH : R ≤ H := hRY.trans hYH
    have hRO : R ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRH hRN' hR2G
    obtain ⟨hcardT, hfaith⟩ := yo2_wreath hTsyl hHtop e
    have hconjmul : ∀ g h : G, (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        (MulAut.conj (g * h)).toMonoidHom := by
      intro g h
      ext x
      simp [mul_assoc]
    have hall : ∀ τ ∈ T ⊓ Subgroup.normalizer (K : Set G), τ ∈ pCoreOf 2 H := by
      rintro τ ⟨hτT, hτK⟩
      have hτH : τ ∈ H := hTH hτT
      have hτH₀ : τ ∈ H₀ := hHH₀ hτH
      obtain ⟨τb, hτb⟩ : ∃ τb, τb = π ⟨τ, hτH₀⟩ := ⟨_, rfl⟩
      have hτR : ∀ r, r ∈ Rb ↔ τb * r * τb⁻¹ ∈ Rb := by
        rw [hτb]
        exact Subgroup.mem_normalizer_iff.mp (hTbN τ hτH₀ hτH)
      obtain ⟨yK, hyK, hyKeq⟩ := hin τ ⟨hτT, hτK⟩
      have hinA : ∃ k ∈ A, ∀ a ∈ A, τb * a * τb⁻¹ = k * a * k⁻¹ := by
        refine ⟨π ⟨yK, hKH₀ hyK⟩, mk_mem_img _ hyK, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (x : G) ∈ K := hx
        have hz := hKo (hyKeq x hx')
        have h1 := hker (⟨τ, hτH₀⟩ * x * ⟨τ, hτH₀⟩⁻¹) (⟨yK, hKH₀ hyK⟩ * x * ⟨yK, hKH₀ hyK⟩⁻¹)
          (by exact hz)
        calc τb * π x * τb⁻¹ = π (⟨τ, hτH₀⟩ * x * ⟨τ, hτH₀⟩⁻¹) := by
              rw [hτb, map_mul, map_mul, map_inv]
          _ = π (⟨yK, hKH₀ hyK⟩ * x * ⟨yK, hKH₀ hyK⟩⁻¹) := h1
          _ = π ⟨yK, hKH₀ hyK⟩ * π x * (π ⟨yK, hKH₀ hyK⟩)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
      have hτK'eq : K'.map (MulAut.conj τ).toMonoidHom = K' := by
        rcases hTsw (τ * t') (T.mul_mem hτT ht'T) with h | h
        · exfalso
          apply ht'n
          have h1 : τ⁻¹ * (τ * t') ∈ Subgroup.normalizer (K : Set G) :=
            Subgroup.mul_mem _ (Subgroup.inv_mem _ hτK) h
          simpa using h1
        · rw [hK', Subgroup.map_map, hconjmul]
          exact h
      have hτ₂T : t'⁻¹ * τ * t' ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ht'T) hτT) ht'T
      have hτ₂K : t'⁻¹ * τ * t' ∈ Subgroup.normalizer (K : Set G) := by
        rw [← A38.map_conj_eq_iff]
        have e1 : K.map (MulAut.conj (t'⁻¹ * τ * t')).toMonoidHom =
            ((K.map (MulAut.conj t').toMonoidHom).map (MulAut.conj τ).toMonoidHom).map
              (MulAut.conj t'⁻¹).toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map, hconjmul, hconjmul, mul_assoc]
        rw [e1, ← hK', hτK'eq, hK', Subgroup.map_map, hconjmul, inv_mul_cancel]
        exact A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)
      obtain ⟨y₂, hy₂K, hy₂eq⟩ := hin (t'⁻¹ * τ * t') ⟨hτ₂T, hτ₂K⟩
      have hinA' : ∃ k ∈ A', ∀ a ∈ A', τb * a * τb⁻¹ = k * a * k⁻¹ := by
        have hy'K' : t' * y₂ * t'⁻¹ ∈ K' := ⟨y₂, hy₂K, by simp [MulAut.conj_apply]⟩
        refine ⟨π ⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩, mk_mem_img _ hy'K', ?_⟩
        rintro _ ⟨x', hx', rfl⟩
        obtain ⟨x, hxK, hxe⟩ := (hx' : (x' : G) ∈ K')
        have hxe' : (x' : G) = t' * x * t'⁻¹ := by
          have := hxe.symm
          simpa [MulAut.conj_apply] using this
        have hz := hKo (hy₂eq x hxK)
        have hz' : t' * ((t'⁻¹ * τ * t' * x * (t'⁻¹ * τ * t')⁻¹) * (y₂ * x * y₂⁻¹)⁻¹) * t'⁻¹ ∈
            pCoreOf 2 H₀ :=
          (Subgroup.mem_normalizer_iff.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀ ht'H₀)
            ((t'⁻¹ * τ * t' * x * (t'⁻¹ * τ * t')⁻¹) * (y₂ * x * y₂⁻¹)⁻¹)).mp hz
        have hz'' : (((⟨τ, hτH₀⟩ * x' * ⟨τ, hτH₀⟩⁻¹ : ↥H₀)) : G) *
            ((⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩ * x' * ⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩⁻¹ : ↥H₀) : G)⁻¹ ∈
              pCoreOf 2 H₀ := by
          have e : (((⟨τ, hτH₀⟩ * x' * ⟨τ, hτH₀⟩⁻¹ : ↥H₀)) : G) *
              ((⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩ * x' * ⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩⁻¹ : ↥H₀) : G)⁻¹ =
              t' * ((t'⁻¹ * τ * t' * x * (t'⁻¹ * τ * t')⁻¹) * (y₂ * x * y₂⁻¹)⁻¹) * t'⁻¹ := by
            show τ * (x' : G) * τ⁻¹ * (t' * y₂ * t'⁻¹ * (x' : G) * (t' * y₂ * t'⁻¹)⁻¹)⁻¹ = _
            rw [hxe']
            group
          rw [e]
          exact hz'
        have h1 := hker _ _ hz''
        calc τb * π x' * τb⁻¹ = π (⟨τ, hτH₀⟩ * x' * ⟨τ, hτH₀⟩⁻¹) := by
              rw [hτb, map_mul, map_mul, map_inv]
          _ = π (⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩ * x' * ⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩⁻¹) := h1
          _ = π ⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩ * π x' * (π ⟨t' * y₂ * t'⁻¹, hK'H₀ hy'K'⟩)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
      have hτ2 : ∃ m : ℕ, τb ^ 2 ^ m = 1 := by
        obtain ⟨m, hm⟩ := hT2 ⟨τ, hτT⟩
        refine ⟨m, ?_⟩
        have h1 : (⟨τ, hτH₀⟩ : ↥H₀) ^ 2 ^ m = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val hm)
        rw [hτb, ← map_pow, h1, map_one]
      have hbd := hbad τb hτR hinA hinA' hτ2
      refine hfaith τ hτT fun y hy => ?_
      have hyH : y ∈ H := hYH hy
      have hyH₀ : y ∈ H₀ := hHH₀ hyH
      obtain ⟨ρ, hρ, hρeq⟩ := hbd (π ⟨y, hyH₀⟩) (mk_mem_img _ hy)
      have hρR : (ρ : G) ∈ R := hρ
      have hρH : (ρ : G) ∈ H := hRH hρR
      have hπu : π (⟨τ, hτH₀⟩ * ⟨y, hyH₀⟩ * ⟨τ, hτH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹ * ρ⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hρeq, ← hτb]
        group
      have h1 : ((⟨τ, hτH₀⟩ * ⟨y, hyH₀⟩ * ⟨τ, hτH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹ * ρ⁻¹ : ↥H₀) : G) ∈
          pCoreOf 2 H₀ := (yo2_mk_one_iff _).mp hπu
      have hmemH : ((⟨τ, hτH₀⟩ * ⟨y, hyH₀⟩ * ⟨τ, hτH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹ * ρ⁻¹ : ↥H₀) : G) ∈ H := by
        show τ * y * τ⁻¹ * y⁻¹ * (ρ : G)⁻¹ ∈ H
        exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hτH hyH) (H.inv_mem hτH)) (H.inv_mem hyH))
          (H.inv_mem hρH)
      have h2 : ((⟨τ, hτH₀⟩ * ⟨y, hyH₀⟩ * ⟨τ, hτH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹ * ρ⁻¹ : ↥H₀) : G) ∈
          pCoreOf 2 H := inf_pCoreOf_le hHH₀ ⟨hmemH, h1⟩
      have e : ⁅τ, y⁆ = ((⟨τ, hτH₀⟩ * ⟨y, hyH₀⟩ * ⟨τ, hτH₀⟩⁻¹ * ⟨y, hyH₀⟩⁻¹ * ρ⁻¹ : ↥H₀) : G) *
          (ρ : G) := by
        show τ * y * τ⁻¹ * y⁻¹ = τ * y * τ⁻¹ * y⁻¹ * (ρ : G)⁻¹ * ρ
        group
      rw [e]
      exact (pCoreOf 2 H).mul_mem h2 (hRO hρR)
    have hidx : Nat.card T ≤ 2 * Nat.card ↥(T ⊓ Subgroup.normalizer (K : Set G)) := by
      refine yo2_card_le_two_mul ht'T fun s hs => ?_
      rcases hTsw s hs with h | h
      · exact Or.inl h
      · right
        rw [← A38.map_conj_eq_iff]
        have e1 : K.map (MulAut.conj (t'⁻¹ * s)).toMonoidHom =
            (K.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t'⁻¹).toMonoidHom := by
          rw [Subgroup.map_map, hconjmul]
        rw [e1, h, hK', Subgroup.map_map, hconjmul, inv_mul_cancel]
        exact A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)
    have hle : Nat.card ↥(T ⊓ Subgroup.normalizer (K : Set G)) ≤ Nat.card ↥(pCoreOf 2 H) :=
      Subgroup.card_le_of_le fun τ hτ => hall τ hτ
    have hpos : 0 < Nat.card ↥(pCoreOf 2 H) := Nat.card_pos
    omega



end CFSG.Quasithin.H13.NF314pt
