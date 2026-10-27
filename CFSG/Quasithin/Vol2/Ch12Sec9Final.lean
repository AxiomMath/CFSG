module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem li128_one (n : ℕ) (L W : Subgroup G) : li128 n 1 L W = lOne L W := by
  unfold li128 lOne
  split_ifs with h
  · omega
  · rfl

theorem mem_normalizer_conjugate_iff {W : Subgroup G} {l x : G} :
    x ∈ normalizer (CFSG.conjugate W l : Set G) ↔ l * x * l⁻¹ ∈ normalizer (W : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (l⁻¹ * y * l)
    rw [SteinbergBS.mem_conjugate_iff, SteinbergBS.mem_conjugate_iff,
      show l * (l⁻¹ * y * l) * l⁻¹ = y by group,
      show l * (x * (l⁻¹ * y * l) * x⁻¹) * l⁻¹ = l * x * l⁻¹ * y * (l * x * l⁻¹)⁻¹ by group]
      at h1
    exact h1
  · intro h y
    rw [SteinbergBS.mem_conjugate_iff, SteinbergBS.mem_conjugate_iff, h (l * y * l⁻¹),
      show l * x * l⁻¹ * (l * y * l⁻¹) * (l * x * l⁻¹)⁻¹ = l * (x * y * x⁻¹) * l⁻¹ by group]

theorem commute_of_mem_omegaOneCenterOf {Γ : Type*} [Group Γ] {Y : Subgroup Γ} {x y : Γ}
    (hx : x ∈ omegaOneCenterOf Y) (hy : y ∈ Y) : x * y = y * x := by
  have h1 : omegaOneCenterOf Y ≤ centerOf Y := (Subgroup.closure_le _).2 fun z hz => hz.1
  exact ((mem_centralizer_iff.1 (h1 hx).2) y hy).symm

theorem config_of_cx1291 (h1222 : Stmt12_2_2) (h1283 : Lemma12_8_3) (h1293 : Lemma12_9_3One)
    (h1294 : Lemma12_9_4) (h1297 : Lemma12_9_7) (h1299 : Lemma12_9_9) (hfin : Final1291)
    [Finite G] {T L V : Subgroup G} {n : ℕ} (hcx : Cx1291 G T L V n) :
    ∃ V Z W H : Subgroup G, IsElementaryAbelian 2 ↥V ∧ V ≤ T ∧ Nat.card V = 2 ^ n ∧
      T ≤ normalizer (V : Set G) ∧
      (∀ Z₁ : Subgroup G, Z₁ ≤ V → Nat.card Z₁ = 2 → ∀ Z₂ : Subgroup G, Z₂ ≤ V →
        Nat.card Z₂ = 2 → ∃ a ∈ normalizer (V : Set G), CFSG.conjugate Z₁ a = Z₂) ∧
      (∀ B : Subgroup G, B ≤ V → ¬ IsCyclic B →
        centralizer (B : Set G) ≤ normalizer (V : Set G)) ∧
      (∀ J : Subgroup G, J ≤ V → Nat.card J = 2 →
        ∀ x ∈ ⨆ h ∈ normalizer (J : Set G), CFSG.conjugate V h,
          ∀ y ∈ ⨆ h ∈ normalizer (J : Set G), CFSG.conjugate V h, x * y = y * x) ∧
      (∀ g : G, CFSG.conjugate V g ≤ T → ⁅V, CFSG.conjugate V g⁆ = ⊥) ∧
      Z ≤ W ∧ W ≤ V ∧ Nat.card Z = 2 ∧ Nat.card W = 4 ∧ T ≤ H ∧
      H ≤ normalizer (Z : Set G) ∧ T ≤ normalizer (W : Set G) ∧
      ¬ H ≤ normalizer
        ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g : Subgroup G) : Set G) ∧
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) ∧
      (∀ x ∈ ⨆ h ∈ H, CFSG.conjugate W h, ∀ y ∈ ⨆ h ∈ H, CFSG.conjugate W h, x * y = y * x) ∧
      (⨆ h ∈ H, CFSG.conjugate W h) ≤ centralizer (V : Set G) ∧
      ⁅⨆ h ∈ H, CFSG.conjugate W h, CFSG.inSubgroup (CFSG.pCore 2) H⁆ ≤ Z ∧
      W < ⨆ h ∈ H, CFSG.conjugate W h := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨hVT, hTV⟩ := hyp.le_and_normalizes h1222
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2)⟩
  have hVel : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq g g.2) }
  obtain ⟨V₁, hV₁⟩ := exists_tsub hT2 hsq hab hTV hcard 1 (by omega)
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one hT2 hsq hab hTV hcard (by omega) hV₁
  obtain ⟨K₁, hLK₁, hK₁c, -⟩ := h1293 G T L V n hcx V₁ hV₁
  obtain ⟨H, hTH, hHK, hHM, hS₃⟩ := hfin G T L V n hcx V₁ K₁ hV₁ hLK₁ hK₁c
  have hK₁N : K₁ ≤ normalizer (V₁ : Set G) := le_of_mem_cComp (show K₁ ∈ cComp _ from hK₁c)
  have hHN : H ≤ normalizer (V₁ : Set G) := hHK.trans (sup_le hK₁N hV₁.2.2)
  have h94 := h1294 G T L V n hcx V₁ hV₁
  obtain ⟨⟨hW₀C, hW₀M⟩, -⟩ := h1299 G T L V n hcx
  have h83 := (h1283 G T L V n hcx.hyp).2.1
  have hu : ∀ x ∈ u128 V V₁, ∀ y ∈ u128 V V₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(u128 V V₁)) ⟨y, hy⟩)
  have hVu : V ≤ u128 V V₁ := le_conjClosure V _
  have hUu : (⨆ h ∈ H, CFSG.conjugate V₂ h) ≤ u128 V V₁ := by
    refine iSup₂_le fun h hh x hx => ?_
    have h1 := SteinbergBS.mem_conjugate_iff.1 hx
    have h2 := mem_conjClosure (Z := V) (H := normalizer (V₁ : Set G)) (inv_mem (hHN hh))
      (hV₂.1 h1)
    rwa [inv_inv, show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h2
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  refine ⟨V, V₁, V₂, H, hVel, hVT, hcard, hTV, ?_, ?_, ?_, ?_, hV₁₂, hV₂.1, hV₁.2.1, hV₂.2.1, hTH,
    hHN, hV₂.2.2, fun h => hHM (h.trans hW₀M), hS₃, ?_, ?_, ?_, ?_⟩
  ·
    intro Z₁ h1 hc1 Z₂ h2 hc2
    obtain ⟨l, hl, hlZ⟩ := h83 1 Z₁ Z₂ h1 h2 (by rw [hc1, pow_one]) (by rw [hc2, pow_one])
    exact ⟨l, hLV hl, hlZ⟩
  ·
    intro B hBV hBc
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 (hVp.to_le hBV)
    have hi2 : 2 ≤ i := by
      by_contra hlt
      apply hBc
      interval_cases i
      · rw [pow_zero, Subgroup.card_eq_one] at hi
        rw [hi]
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hi
        exact isCyclic_of_prime_card hi
    have hin : i ≤ n := by
      have h1 := Subgroup.card_le_of_le hBV
      rw [hi, hcard] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    rcases eq_or_lt_of_le hin with rfl | hlt
    · have hBeq : B = V := Subgroup.eq_of_le_of_card_ge hBV (by rw [hi, hcard])
      rw [hBeq]
      exact Subgroup.centralizer_le_normalizer _
    · obtain ⟨Vi, hVi⟩ := exists_tsub hT2 hsq hab hTV hcard i hin
      obtain ⟨l, hl, hlB⟩ := h83 i Vi B hVi.1 hBV hVi.2.1 hi
      have h97 := h1297 G _ L V n hcx i Vi (by omega) hlt hVi
      intro c hc
      have hcB : c ∈ normalizer (B : Set G) := Subgroup.centralizer_le_normalizer _ hc
      rw [← hlB, mem_normalizer_conjugate_iff] at hcB
      have h1 := (h97 hcB).2
      have h2 : l⁻¹ * (l * c * l⁻¹) * l⁻¹⁻¹ ∈ normalizer (V : Set G) :=
        mul_mem (mul_mem (inv_mem (hLV hl)) h1) (inv_mem (inv_mem (hLV hl)))
      rwa [show l⁻¹ * (l * c * l⁻¹) * l⁻¹⁻¹ = c by group] at h2
  ·
    intro Z hZV hZ2
    obtain ⟨l, hl, hlZ⟩ := h83 1 V₁ Z hV₁.1 hZV hV₁.2.1 (by rw [hZ2, pow_one])
    have hlV : l ∈ normalizer (V : Set G) := hLV hl
    have key : ∀ x ∈ ⨆ h ∈ normalizer (Z : Set G), CFSG.conjugate V h,
        l * x * l⁻¹ ∈ u128 V V₁ := by
      have hle : (⨆ h ∈ normalizer (Z : Set G), CFSG.conjugate V h) ≤
          (u128 V V₁).comap (MulAut.conj l).toMonoidHom := by
        refine iSup₂_le fun h hh y hy => ?_
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hh' : l * h * l⁻¹ ∈ normalizer (V₁ : Set G) := by
          rw [← hlZ] at hh
          exact mem_normalizer_conjugate_iff.1 hh
        have hy' := SteinbergBS.mem_conjugate_iff.1 hy
        have hv : l * (h * y * h⁻¹) * l⁻¹ ∈ V := (mem_normalizer_iff.1 hlV _).1 hy'
        have h1 := mem_conjClosure (Z := V) (H := normalizer (V₁ : Set G)) (inv_mem hh') hv
        rwa [show (l * h * l⁻¹)⁻¹ * (l * (h * y * h⁻¹) * l⁻¹) * (l * h * l⁻¹)⁻¹⁻¹ =
          l * y * l⁻¹ by group] at h1
      intro x hx
      have h1 := hle hx
      rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    intro x hx y hy
    have h1 := hu _ (key x hx) _ (key y hy)
    calc x * y = l⁻¹ * ((l * x * l⁻¹) * (l * y * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * y * l⁻¹) * (l * x * l⁻¹)) * l := by rw [h1]
      _ = y * x := by group
  ·
    intro g hg
    have h1 : CFSG.conjugate V g ≤ centralizer (V : Set G) :=
      (le_iSup₂ (f := fun g (_ : CFSG.conjugate V g ≤ (S : Subgroup G)) => CFSG.conjugate V g)
        g hg).trans hW₀C
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 h1
  ·
    intro x hx y hy
    exact hu x (hUu hx) y (hUu hy)
  ·
    intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    exact hu v (hVu hv) x (hUu hx)
  ·
    have hSH : (S : Subgroup G) ≤ H := hTH
    have hV₁H : V₁ ≤ H := hV₁.1.trans (hVT.trans hSH)
    have hV₁p : IsPGroup 2 V₁ := hVp.to_le hV₁.1
    have hV₁ne : V₁ ≠ ⊥ := fun h => by
      have := hV₁.2.1
      rw [h, Subgroup.card_bot] at this
      norm_num at this
    have hO₂ : V₁ ≤ pCoreOf 2 H :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV₁H hHN hV₁p
    have hlOne : lOne (⊥ : Subgroup G) V₁ = ⊥ :=
      le_bot_iff.1 ((oTwoUpper_le _).trans inf_le_left)
    have hsylH : QuasithinUnique.IsSylowTwoOf (S : Subgroup G) H :=
      ⟨hSH, S.isPGroup', fun h => hyp.sylow.2 (h.trans (by
        simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hSH))⟩
    have hV₁₂lt : V₁ < V₂ := by
      refine lt_of_le_of_ne hV₁₂ fun h => ?_
      have h1 := hV₂.2.1
      rw [← h, hV₁.2.1] at h1
      norm_num at h1
    have hASH : AlmostSpecialHyp V₂ V₁ ⊥ (S : Subgroup G) H :=
      { elemAbelian := ⟨⟨⟨fun a b => Subtype.ext (hab _ (hV₂.1 a.2) _ (hV₂.1 b.2))⟩⟩,
          fun x hx => hsq x (hV₂.1 hx)⟩
        ne_bot := hV₁ne
        le_V := hV₁₂
        oTwo_eq := (le_bot_iff.1 (oTwoUpper_le ⊥)).symm
        V_le_T := hV₂.1.trans hVT
        T_le_normV₁ := hV₁.2.2
        T_le_normV := hV₂.2.2
        T_le_normL := by
          rw [normalizer_eq_top_iff.2 inferInstance]
          exact le_top
        sylow_LT := by
          rw [bot_sup_eq]
          exact ⟨le_rfl, S.isPGroup', by simp⟩
        H_le := hHN
        lOne_sup_le := by
          rw [hlOne, bot_sup_eq]
          exact hSH
        sylow_H := hsylH
        charTwo := charTwo_of_inH hyp.qtke.2.1 S ⟨hSH, fun h => hV₁ne (le_bot_iff.1 (h ▸ hO₂))⟩
        irred := by
          refine ⟨hV₁₂lt, ?_, ?_, fun W hW₁ hW₂ _ => ?_⟩
          · rw [hlOne, bot_sup_eq]
            exact hV₂.2.2
          · rw [hlOne, bot_sup_eq]
            exact hV₁.2.2
          · have hd : Nat.card W ∣ 2 ^ 2 := by
              rw [← hV₂.2.1]
              exact Subgroup.card_dvd_of_le hW₂
            have hd' : 2 ^ 1 ∣ Nat.card W := by
              rw [← hV₁.2.1]
              exact Subgroup.card_dvd_of_le hW₁
            obtain ⟨m, hm, hWm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
            interval_cases m
            · rw [hWm] at hd'
              norm_num at hd'
            · exact Or.inl (Subgroup.eq_of_le_of_card_ge hW₁ (hWm.trans hV₁.2.1.symm).le).symm
            · exact Or.inr (Subgroup.eq_of_le_of_card_ge hW₂ (hV₂.2.1.trans hWm.symm).le) }
    have hG22 := hASH.G22_one.2
    have hUcc : (⨆ h ∈ H, CFSG.conjugate V₂ h) ≤ conjClosure V₂ H := by
      refine iSup₂_le fun h hh x hx => ?_
      have h1 := SteinbergBS.mem_conjugate_iff.1 hx
      have h2 := mem_conjClosure (Z := V₂) (H := H) (inv_mem hh) h1
      rwa [inv_inv, show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h2
    have hccH : conjClosure V₂ H ≤ H := conjClosure_le fun h hh v hv =>
      H.mul_mem (H.mul_mem hh (hV₂.1.trans (hVT.trans hSH) hv)) (H.inv_mem hh)
    have hQeq : CFSG.inSubgroup (CFSG.pCore 2) H = pCoreOf 2 H := by
      show (CFSG.pCore 2 ↥H).map H.subtype = (CFSG.Open.pCore 2 ↥H).map H.subtype
      try with_reducible rfl
    rw [hQeq, Subgroup.commutator_le]
    intro u hu q hq
    have hu' : u ∈ conjClosure V₂ H := hUcc hu
    have huN : u ∈ normalizer (V₁ : Set G) := hHN (hccH hu')
    have hqN : q ∈ normalizer (V₁ : Set G) := hHN (LieType.BorelTits.pCoreOf_le 2 H hq)
    have h1 : tmk V₁ ⟨u, huN⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
      hG22 (secMk_mem_secImg hu')
    have h2 : tmk V₁ ⟨q, hqN⟩ ∈ tildeOf V₁ (pCoreOf 2 H) := secMk_mem_secImg hq
    have h3 := commute_of_mem_omegaOneCenterOf h1 h2
    have h4 : tmk V₁ (⟨u, huN⟩ * ⟨q, hqN⟩ * ⟨u, huN⟩⁻¹ * ⟨q, hqN⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h3]
      group
    have h5 := secMk_eq_one_iff.1 h4
    simpa [commutatorElement_def] using h5
  ·
    refine lt_of_le_of_ne ?_ fun heq => hHM ?_
    · have := le_iSup₂ (f := fun h (_ : h ∈ H) => CFSG.conjugate V₂ h) 1 H.one_mem
      rwa [SteinbergBS.conjugate_one] at this
    · intro h hh
      have h1 : CFSG.conjugate V₂ h ≤ V₂ :=
        (le_iSup₂ (f := fun h (_ : h ∈ H) => CFSG.conjugate V₂ h) h hh).trans heq.symm.le
      have h2 : CFSG.conjugate V₂ h = V₂ := Subgroup.eq_of_le_of_card_ge h1 (by
        rw [LinearS3.card_conjugate])
      have h3 := SteinbergBS.mem_normalizer_of_conjugate_eq h2
      exact (h1297 G (S : Subgroup G) L V n hcx 2 V₂ (by omega) (by omega) hV₂ h3).1

theorem false_of_cx1291 (h1222 : Stmt12_2_2) (h1283 : Lemma12_8_3) (h1293 : Lemma12_9_3One)
    (h1294 : Lemma12_9_4) (h1297 : Lemma12_9_7) (h1299 : Lemma12_9_9) (hfin : Final1291)
    [Finite G] {T L V : Subgroup G} {n : ℕ} (hcx : Cx1291 G T L V n) : False := by
  obtain ⟨V', Z, W, H, hVel, hVT, hVn, hTV, htrans, hcent, hhull, hwc, hZW, hWV, hZ, hW, hTH,
    hHZ, hTW, hHW₀, hS₃, hUab, hUV, hUQ, hWU⟩ :=
    config_of_cx1291 h1222 h1283 h1293 h1294 h1297 h1299 hfin hcx
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hcx.hyp.hyp.sylow
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  exact LinearS3.linear_S3_abelian_hull_obstruction S hVn hn4 hVT hTV htrans hcent hhull hwc hZW
    hWV hZ hW hTH hHZ hTW hHW₀ hS₃ hUab hUV hUQ hWU

end CFSG.Quasithin.H13
