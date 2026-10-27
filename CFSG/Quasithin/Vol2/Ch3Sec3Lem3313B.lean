module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313
public import CFSG.Quasithin.Vol2.Ch3Sec3BenderCore
public import CFSG.Quasithin.Vol2.Ch3Sec3CZCore
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)

namespace Lem3313B

open CFSG.Quasithin.H13.BenL2 CFSG.Quasithin.H13.BenC

theorem mem_normalizer_of_odd {Q : Type} [Group Q] (h37 : A37Statement Q) {A A' : Subgroup Q}
    (hA : A ∈ cComp (⊤ : Subgroup Q)) (hA' : A' ∈ cComp (⊤ : Subgroup Q)) (hne : A ≠ A')
    {d : Q} (hd : d ∈ Subgroup.normalizer ((A ⊔ A' : Subgroup Q) : Set Q))
    (ho : Odd (orderOf d)) :
    d ∈ Subgroup.normalizer (A : Set Q) ∧ d ∈ Subgroup.normalizer (A' : Set Q) := by
  set c : Subgroup Q → Subgroup Q := fun X => X.map (MulAut.conj d).toMonoidHom with hc
  have hinj : ∀ X Y : Subgroup Q, c X = c Y → X = Y := fun X Y h =>
    Subgroup.map_injective (MulAut.conj d).injective h
  have hsup : c (A ⊔ A') = A ⊔ A' := A38.map_conj_eq_iff.mpr hd
  have hcases : ∀ X : Subgroup Q, X ∈ cComp (⊤ : Subgroup Q) → X ≤ A ⊔ A' → c X = A ∨ c X = A' :=
    by
    intro X hX hXle
    refine C2A3Orbits.eq_or_eq_of_le_sup h37 hA hA' (C2A3Orbits.conj_mem_cComp_top hX d) ?_
    rw [← hsup]
    exact Subgroup.map_mono hXle
  have hcA := hcases A hA le_sup_left
  have hcA' := hcases A' hA' le_sup_right
  have hdA : d ∈ Subgroup.normalizer (A : Set Q) := by
    rcases hcA with h | h
    · exact A38.map_conj_eq_iff.mp h
    · exfalso
      have h2 : c A' = A := by
        rcases hcA' with h' | h'
        · exact h'
        · exact absurd (hinj _ _ (h.trans h'.symm)) hne
      have hdd : d * d ∈ Subgroup.normalizer (A : Set Q) := by
        refine A38.map_conj_eq_iff.mp ?_
        have e : (MulAut.conj (d * d)).toMonoidHom =
            (MulAut.conj d).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
          ext x
          simp [mul_assoc]
        rw [e, ← Subgroup.map_map]
        show c (c A) = A
        rw [h, h2]
      have hz : d ∈ Subgroup.zpowers (d ^ 2) :=
        A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr ho)
      have hdA : d ∈ Subgroup.normalizer (A : Set Q) := by
        refine (Subgroup.zpowers_le.mpr ?_) hz
        rw [pow_two]
        exact hdd
      have h3 : c A = A := A38.map_conj_eq_iff.mpr hdA
      exact hne (h3.symm.trans h)
  refine ⟨hdA, ?_⟩
  have h1 : c A = A := A38.map_conj_eq_iff.mpr hdA
  rcases hcA' with h' | h'
  · exact absurd (hinj _ _ (h1.trans h'.symm)) hne
  · exact A38.map_conj_eq_iff.mp h'

theorem mem_normalizer_sup {Q : Type*} [Group Q] {d : Q} {X₁ X₂ : Subgroup Q}
    (h1 : d ∈ Subgroup.normalizer (X₁ : Set Q)) (h2 : d ∈ Subgroup.normalizer (X₂ : Set Q)) :
    d ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

section Image

variable {G : Type} [Group G] {H₀ : Subgroup G}

theorem mk_mem_img {X : Subgroup G} (x : ↥H₀) (hx : (x : G) ∈ X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) x ∈ modO2Image H₀ X :=
  ⟨x, hx, rfl⟩

theorem img_le_normalizer {X Y : Subgroup G}
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    modO2Image H₀ X ≤ Subgroup.normalizer ((modO2Image H₀ Y : Subgroup _) : Set _) := by
  have key : ∀ x : ↥H₀, (x : G) ∈ X → ∀ z ∈ modO2Image H₀ Y,
      QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) x * z * (QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) x)⁻¹ ∈
        modO2Image H₀ Y := by
    intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨x * y * x⁻¹, ?_, by simp⟩
    show (x : G) * y * (x : G)⁻¹ ∈ Y
    exact (Subgroup.mem_normalizer_iff.mp (h hx) y).mp hy
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key x hx z, fun hz => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hz
  simpa [mul_assoc] using this

theorem img_mono {Y Z : Subgroup G} (h : Y ≤ Z) : modO2Image H₀ Y ≤ modO2Image H₀ Z :=
  fun _ ⟨x, hx, hxe⟩ => ⟨x, h hx, hxe⟩

theorem img_sup {A B : Subgroup G} (hA : A ≤ H₀) (hB : B ≤ H₀) :
    modO2Image H₀ (A ⊔ B) = modO2Image H₀ A ⊔ modO2Image H₀ B := by
  unfold modO2Image
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem relIndex_map_le {Γ Γ' : Type*} [Group Γ] [Group Γ'] [Finite Γ] (f : Γ →* Γ')
    (A B : Subgroup Γ) : (A.map f).relIndex (B.map f) ≤ A.relIndex B := by
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_le_of_le_left (Subgroup.le_comap_map f A)
    (Subgroup.index_ne_zero_of_finite (H := A.subgroupOf B))

end Image

theorem step3_3_13Bender_of (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) : Step3_3_13Bender := by
  intro G _ _ T M L D H K h hH ⟨e⟩ hO hK hKq hYK hTK ⟨n, hn, hmod⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  have hTH : T ≤ H := hH.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow hTH⟩
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hTH.trans le_sup_left)⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  set φ := oTwoQuotEquiv e with hφ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXi := Der6D.xi_of_iso hTsyl hH.2 φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)
  have hOHT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ T := fun x hx =>
    hOHT (C1Pack12.pow_three_mem_pCoreOf φ hx)
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHN : H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKc h37 h38 hO hT₀ hK
  set H₀ := H ⊔ D with hH₀
  have hHH₀ : H ≤ H₀ := le_sup_left
  have hDH₀ : D ≤ H₀ := le_sup_right
  have hTH₀ : T ≤ H₀ := hTH.trans hHH₀
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKc hO
  have h37Q := h37 _ hQ
  have h38Q := h38 _ hQ
  set π : ↥H₀ →* ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥H₀, π x = 1 → (x : G) ∈ T := by
    intro x hx
    have h1 : x ∈ CFSG.Open.pCore 2 ↥H₀ := by
      exact (QuotientGroup.eq_one_iff x).mp hx
    exact pCoreOf_le_of_isSylowTwoOf hT₀ ⟨x, h1, rfl⟩
  set Ab := modO2Image H₀ K with hAb
  set Tb := modO2Image H₀ T with hTbdef
  have hAbc : Ab ∈ cComp (⊤ : Subgroup _) := modO2Image_mem_cComp hK
  have hTb : IsSylowTwoOf Tb ⊤ :=
    A312.isSylowTwoOf_top_map π hπs (isSylowTwoOf_top_subgroupOf hT₀)
  obtain ⟨-, hT38⟩ := h38Q Ab hAbc
  rcases hT38 Tb hTb with ⟨hnorm, -, -⟩ |
      ⟨tb, htb, htbn, hconjT, -, hcomm, hinf, hTbN, hsupT⟩
  ·
    exfalso
    apply hTK
    intro t ht
    have htH : t ∈ H₀ := hTH₀ ht
    have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
    have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) = modO2Image H₀ K := by
      refine (modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩).trans ?_
      refine A38.map_conj_eq_iff.mpr ?_
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top _
    exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
  set Ab' := Ab.map (MulAut.conj tb).toMonoidHom with hAb'
  have hAb'c : Ab' ∈ cComp (⊤ : Subgroup _) := C2A3Orbits.conj_mem_cComp_top hAbc tb
  have hne : Ab ≠ Ab' := fun h1 => htbn (A38.map_conj_eq_iff.mp h1.symm)
  have hcomm' : ∀ a ∈ Ab, ∀ b ∈ Ab', a * b = b * a := by
    intro a ha b hb
    have h1 : Ab ≤ Subgroup.centralizer (Ab' : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (h1 ha) b hb).symm
  have htA : ∀ a, a ∈ Ab ↔ tb * a * tb⁻¹ ∈ Ab' := by
    intro a
    rw [hAb', A38.mem_map_conj]
    simp [mul_assoc]
  have hn1 : 1 ≤ n := hmod.1.2.1
  have hn2 : 2 ≤ n := by
    obtain ⟨m, rfl⟩ := hn
    omega
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  obtain ⟨e₂⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2 2 n
    hmod
  have hL2 : L2Facts ↥Ab (2 ^ n) := L2Facts.of_mulEquiv (e₁.symm.trans e₂) (l2Facts_psl2 hF hn)
  have hL2' : L2Facts ↥Ab' (2 ^ n) :=
    L2Facts.of_mulEquiv (Subgroup.equivMapOfInjective Ab (MulAut.conj tb).toMonoidHom
      (MulAut.conj tb).injective).symm hL2
  have hBA := borelL2_of_l2Facts hL2
  have hBA' := borelL2_of_l2Facts hL2'
  have hAN : Ab ≤ Subgroup.normalizer ((Ab ⊔ Ab' : Subgroup _) : Set _) := fun a ha =>
    mem_normalizer_sup (Subgroup.le_normalizer ha) (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm' a ha b hb).symm))
  have hTbAT : IsSylowTwoOf Tb (Ab ⊔ Tb) := ⟨le_sup_right, hTb.2.1, fun h2 => hTb.2.2
    (h2.trans (by
      show Tb.relIndex (Ab ⊔ Tb) ∣ Tb.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hS0 : IsSylowTwoOf (Tb ⊓ (Ab ⊔ Ab')) (Ab ⊔ Ab') :=
    A4.isSylowTwoOf_inf_normal hTbAT (by rw [hsupT]; exact le_sup_left) (sup_le hAN hTbN)
  have hAAN : Ab ⊔ Ab' ≤ Subgroup.normalizer (Ab : Set _) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_comm hcomm')
  have hAAN' : Ab ⊔ Ab' ≤ Subgroup.normalizer (Ab' : Set _) :=
    sup_le (le_normalizer_of_comm (fun a ha b hb => (hcomm' b hb a ha).symm))
      Subgroup.le_normalizer
  have hS : IsSylowTwoOf (Tb ⊓ Ab) Ab := by
    have h1 := A4.isSylowTwoOf_inf_normal hS0 le_sup_left hAAN
    rwa [inf_assoc, inf_of_le_right (le_sup_left : Ab ≤ Ab ⊔ Ab')] at h1
  have hS' : IsSylowTwoOf (Tb ⊓ Ab') Ab' := by
    have h1 := A4.isSylowTwoOf_inf_normal hS0 le_sup_right hAAN'
    rwa [inf_assoc, inf_of_le_right (le_sup_right : Ab' ≤ Ab ⊔ Ab')] at h1
  obtain ⟨⟨t₀, ht₀H⟩, ht₀T, rfl⟩ := htb
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H₀ := map_conj_mem_cComp hK ht₀H
  have hK'b : modO2Image H₀ K' = Ab' := modO2Image_conj ⟨t₀, ht₀H⟩
  have hKK : conjClosure K T = K ⊔ K' := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (sup_le (le_conjClosure K T) ?_)
    · have htH : t ∈ H₀ := hTH₀ ht
      have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
      have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) ∈ conjSubgroupsBy Tb Ab := by
        rw [modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩]
        exact ⟨π ⟨t, htH⟩, mk_mem_img _ ht, rfl⟩
      rw [hconjT] at h2
      have hmem : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
      rcases h2 with h2 | h2
      · rw [modO2Image_injOn H₀ h1 hK h2] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [Set.mem_singleton_iff, ← hK'b] at h2
        rw [modO2Image_injOn H₀ h1 hK'c h2] at hmem
        exact Subgroup.mem_sup_right hmem
    · rintro _ ⟨k, hk, rfl⟩
      exact mem_conjClosure (show t₀ ∈ T from ht₀T) hk
  have hKKH₀ : K ⊔ K' ≤ H₀ := sup_le (le_of_mem_cComp hK) (le_of_mem_cComp hK'c)
  have hKKb : modO2Image H₀ (K ⊔ K') = Ab ⊔ Ab' := by
    rw [img_sup (le_of_mem_cComp hK) (le_of_mem_cComp hK'c), hK'b]
  set Ub := modO2Image H₀ (pCoreOf 2 H) with hUb
  set Yb := modO2Image H₀ (oTwoUpper H) with hYb
  set Pb := modO2Image H₀ P3 with hPb
  set Db := modO2Image H₀ D with hDb
  have hTU : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hYU : oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hYH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hTY : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper H)
  have hUbT : Ub ≤ Tb := img_mono hOHT
  have hU8 : Ub.relIndex Tb ≤ 8 := by
    have h1 := relIndex_map_le π ((pCoreOf 2 H).subgroupOf H₀) (T.subgroupOf H₀)
    rw [Subgroup.relIndex_subgroupOf hTH₀] at h1
    refine h1.trans ?_
    rw [← Subgroup.inf_relIndex_left, C1Pack12.relIndex_inf_pCoreOf_eq_card hTH]
    have h2 : IsPGroup 2 ↥(imageOTwoQuot H T) :=
      (A4.isPGroup_subgroupOf_of_le hTH hT2).map _
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2
    have h3 : Nat.card ↥(imageOTwoQuot H T) ∣ 72 := by
      rw [← S152N.W3.card_eq, ← Nat.card_congr φ.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hm] at h3 ⊢
    have h4 : 2 ^ m ∣ 8 :=
      (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 9)).dvd_of_dvd_mul_right
        (by simpa using h3)
    exact Nat.le_of_dvd (by norm_num) h4
  have hYbA : Yb ≤ Ab ⊔ Ab' := by
    rw [← hKKb]
    exact img_mono (hYK.trans hKK.le)
  have hPbY : Pb ≤ Yb := img_mono hP3.1
  have hPb3 : IsPGroup 3 Pb :=
    (hP3.2.1.comap_of_injective H₀.subtype H₀.subtype_injective).map _
  have hPb9 : Nat.card Pb = 9 := by
    rw [← hP3card]
    have hinj : Function.Injective (π.comp (P3.subgroupOf H₀).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ((x : ↥H₀) : G) ∈ T := hker _ hx
      have h2 : ((x : ↥H₀) : G) ∈ P3 := x.2
      have h3 : ((x : ↥H₀) : G) ∈ P3 ⊓ T := ⟨h2, h1⟩
      rw [(IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 T hP3.2.1 hT2).eq_bot,
        Subgroup.mem_bot] at h3
      exact Subtype.ext (Subtype.ext h3)
    have h1 : Pb = (π.comp (P3.subgroupOf H₀).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      try rfl
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP3.1.trans (hYH.trans hHH₀))).toEquiv
  have hYb3 : ∀ y ∈ Yb, y ^ 3 ∈ Tb := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    exact mk_mem_img _ (by simpa using hpow3 _ hy)
  have hDodd : ∀ x ∈ Db, Odd (orderOf x) := by
    rintro _ ⟨d, hd, rfl⟩
    refine Odd.of_dvd_nat h.Dodd ?_
    refine (orderOf_map_dvd π d).trans ?_
    have h1 : orderOf d = orderOf ((d : G)) := Subgroup.orderOf_coe d |>.symm
    have h2 : orderOf ((⟨d, hd⟩ : ↥D)) = orderOf (d : G) := Subgroup.orderOf_mk _ _
    rw [h1, ← h2]
    exact orderOf_dvd_natCard _
  have hDN : Db ≤ Subgroup.normalizer ((Ab ⊔ Ab' : Subgroup _) : Set _) := by
    rw [← hKKb]
    refine img_le_normalizer ?_
    rw [← hKK]
    exact hDH₀.trans hHN
  have hDA : Db ≤ Subgroup.normalizer (Ab : Set _) := fun x hx =>
    (mem_normalizer_of_odd h37Q hAbc hAb'c hne (hDN hx) (hDodd x hx)).1
  have hDA' : Db ≤ Subgroup.normalizer (Ab' : Set _) := fun x hx =>
    (mem_normalizer_of_odd h37Q hAbc hAb'c hne (hDN hx) (hDodd x hx)).2
  have hDT : Db ≤ Subgroup.normalizer (Tb : Set _) := img_le_normalizer h.DN
  have hcore := le_normalizer_core hBA hBA' hq hcomm' hinf hS hS' hTb.2.1
    (mk_mem_img (X := T) ⟨t₀, ht₀H⟩ ht₀T) htA hUbT hU8 (img_le_normalizer hTU) hYbA
    (img_le_normalizer hYU) (img_le_normalizer hTY) hPbY hPb3 hPb9 hYb3 hDA hDA'
    hDT
  set Rb := Yb ⊔ (Tb ⊓ Ab ⊔ Tb ⊓ Ab') with hRb
  set R := (Rb.comap π).map H₀.subtype with hR
  have hRmem : ∀ g : G, g ∈ R ↔ ∃ hg : g ∈ H₀, π ⟨g, hg⟩ ∈ Rb := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, hgR⟩
      exact ⟨⟨g, hg⟩, hgR, rfl⟩
  have hYR : oTwoUpper H ≤ R := fun y hy =>
    (hRmem y).mpr ⟨hHH₀ (hYH hy), Subgroup.mem_sup_left (mk_mem_img _ hy)⟩
  have hRYT : R ≤ oTwoUpper H ⊔ T := by
    intro g hg
    obtain ⟨hgH, hgR⟩ := (hRmem g).mp hg
    have hTYb : Tb ≤ Subgroup.normalizer (Yb : Set _) := img_le_normalizer hTY
    have hWT : Tb ⊓ Ab ⊔ Tb ⊓ Ab' ≤ Tb := sup_le inf_le_left inf_le_left
    have h1 : π ⟨g, hgH⟩ ∈ Yb ⊔ Tb := sup_le_sup_left hWT Yb hgR
    obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨τ, hτ, rfl⟩, hyτ⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer hTYb).mp h1
    have h2 : π ((y * τ)⁻¹ * ⟨g, hgH⟩) = 1 := by
      rw [map_mul, map_inv, map_mul, hyτ, inv_mul_cancel]
    have h3 := hker _ h2
    have e : g = (y : G) * τ * ((((y * τ)⁻¹ * ⟨g, hgH⟩ : ↥H₀)) : G) := by
      simp [mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right hτ)) (Subgroup.mem_sup_right h3)
  have hO2R : oTwoUpper R = oTwoUpper H := by
    refine le_antisymm ?_ ?_
    · rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hx, ho⟩
      exact CZCore.mem_of_odd hTY hT2 (hRYT hx) ho
    · have h1 : oTwoUpper H = oTwoUpper (oTwoUpper H) := hXi.1
      rw [h1]
      exact oTwoUpper_mono hYR
  have hDR : D ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ d ∈ D, ∀ g ∈ R, d * g * d⁻¹ ∈ R := by
      intro d hd g hg
      obtain ⟨hgH, hgR⟩ := (hRmem g).mp hg
      have hdH : d ∈ H₀ := hDH₀ hd
      refine (hRmem _).mpr ⟨H₀.mul_mem (H₀.mul_mem hdH hgH) (H₀.inv_mem hdH), ?_⟩
      have e : (⟨d * g * d⁻¹, H₀.mul_mem (H₀.mul_mem hdH hgH) (H₀.inv_mem hdH)⟩ : ↥H₀) =
          ⟨d, hdH⟩ * ⟨g, hgH⟩ * (⟨d, hdH⟩ : ↥H₀)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hcore (mk_mem_img _ hd)) _).mp hgR
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key d hd g, fun hg => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hg
    simpa [mul_assoc] using this
  rw [← hO2R]
  exact hDR.trans (normalizer_le_normalizer_oTwoUpper R)

end Lem3313B

end CFSG.Quasithin.H13
