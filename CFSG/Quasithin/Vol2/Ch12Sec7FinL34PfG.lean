module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34
public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfB
public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfC
public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfF
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.Vol2.Ch12Sec7FinJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped commutatorElement

namespace L34Br

theorem comap_pCore_eq' {A C : Type*} [Group A] [Group C] [Finite A] [Finite C] {f : A →* C}
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    (CFSG.pCore 2 C).comap f = CFSG.pCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : IsPGroup 2 (CFSG.pCore 2 C) := CFSG.pCore_isPGroup
  have hPA : IsPGroup 2 (CFSG.pCore 2 A) := CFSG.pCore_isPGroup
  refine le_antisymm ?_ ?_
  · have hn : ((CFSG.pCore 2 C).comap f).Normal := CFSG.pCore_normal.comap f
    exact le_sSup ⟨hn, hPC.comap_of_ker_isPGroup f hker⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((CFSG.pCore 2 A).map f).Normal := CFSG.pCore_normal.map f hf
    exact le_sSup ⟨hn, hPA.map f⟩

theorem nonempty_quot_pCore_equiv {A C : Type*} [Group A] [Group C] [Finite A] [Finite C]
    {f : A →* C} (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nonempty ((A ⧸ CFSG.pCore 2 A) ≃* (C ⧸ CFSG.pCore 2 C)) := by
  let g : A →* C ⧸ CFSG.pCore 2 C := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = CFSG.pCore 2 A := by
    rw [← comap_pCore_eq' hf hker]
    ext x
    simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

theorem isPSL_oTwoUpper_of_equiv {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁]
    (e : Q₁ ≃* Q₂) {n p r : ℕ} (h : IsPSL n p r ↥(oTwoUpper (⊤ : Subgroup Q₂))) :
    IsPSL n p r ↥(oTwoUpper (⊤ : Subgroup Q₁)) := by
  have hmap : (oTwoUpper (⊤ : Subgroup Q₁)).map e.toMonoidHom = oTwoUpper (⊤ : Subgroup Q₂) := by
    rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ e.surjective]
  exact isPSL_of_mulEquiv h ((Subgroup.equivMapOfInjective _ _ e.injective).trans
    (MulEquiv.subgroupCongr hmap)).symm

theorem open_pCore_quot_eq_bot (X : Type) [Group X] [Finite X] :
    CFSG.Open.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := QuotientGroup.mk' (CFSG.pCore 2 X)
  have hker : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have h := comap_pCore_eq' (QuotientGroup.mk'_surjective (CFSG.pCore 2 X)) hker
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ (CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X)).comap f :=
    (CFSG.pCore_eq_open _ 2).ge hy
  rw [h] at hx
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).2 hx

end L34Br

open L34Br S127 in
theorem final1271L34Data_of (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) :
    Final1271L34Data := by
  intro G _ _ T L V t z hS H hHs hHz hK hL1T g hgT hgO
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy := hS.hyp.hyp
  obtain ⟨hcomm, -, hTV⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hy hv⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set A := conjSubgroup V g with hAdef
  have hAe : IsElemAbelian 2 A := isElemAbelian_conjSubgroup hVe g
  have hTH : T ≤ H := hHs.1.1
  have hTM : T ≤ M := hy.normalizes
  have hTsyl : IsSylowIn 2 T H :=
    ⟨hTH, hy.sylow.1, fun h => hy.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hAT : A ≤ T := hgT.trans inf_le_left
  have hAH : A ≤ H := hAT.trans hTH
  have hOT : pCoreOf 2 H ≤ T := hTsyl.le_of_normal (pCoreOf_le 2 H)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).2
      (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  set O := CFSG.pCore 2 ↥H with hO
  set f := QuotientGroup.mk' O with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective O
  have hfker : f.ker = O := QuotientGroup.ker_mk' O
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hOsub : O = (pCoreOf 2 H).subgroupOf H := by
    rw [hO]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hOTs : O ≤ T.subgroupOf H := by
    rw [hOsub]
    intro x hx
    exact hOT hx
  set K := oTwoUpper (⊤ : Subgroup (↥H ⧸ O)) with hKdef
  have hKn : K.Normal := oTwoUpper_top_normal'
  have hOY := open_pCore_quot_eq_bot ↥H
  have hKs : IsSimpleGroup ↥K := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hK).2
  have h20160 : Nat.card ↥K = 20160 := by
    rw [GoldS146R.card_of_isPSL hK]
    decide
  have hKnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup ↥K := { (inferInstance : Group ↥K) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥K)
    rw [h20160] at hp
    exact absurd hp (by norm_num)
  have hC := centralizer_oTwoUpper_eq_bot hOY hKs hKnc
  have hLie : CFSG.Blueprint.LieModel ↥K .PSL 3 2 2 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hK⟩
  set S := (T.subgroupOf H).map f with hSdef
  have hTsub : IsSylowIn 2 (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
    have := (E1.isSylowIn_subgroupOf_iff hTH (le_refl H)).2 hTsyl
    rwa [Subgroup.subgroupOf_self] at this
  have hSsyl : IsSylowIn 2 S ⊤ := E1.isSylowIn_two_map_top hfs hTsub
  have hTcomap : S.comap f = T.subgroupOf H :=
    Subgroup.comap_map_eq_self (by rw [hfker]; exact hOTs)
  have hSK := isSylowIn_inf_oTwoUpper hSsyl
  have hS₀ : QuasithinUnique.IsSylowTwoOf (S.subgroupOf K) (⊤ : Subgroup ↥K) := by
    have h := (E1.isSylowIn_subgroupOf_iff (inf_le_right : S ⊓ K ≤ K) (le_refl K)).2 hSK
    rw [Subgroup.subgroupOf_self, Subgroup.inf_subgroupOf_right] at h
    exact h
  have hpar : ParY S := parY_of (l34ParData_of hLie hS₀)
  have hout : OutY S := outY_of hC (l34OutData_of hLie hS₀)
  set E := (A.subgroupOf H).map f with hEdef
  have hES : E ≤ S := Subgroup.map_mono (fun x hx => hAT hx)
  have hEe : IsElemAbelian 2 E := isElemAbelian_map f (isElemAbelian_subgroupOf' hAe)
  have hE1 : E ≠ ⊥ := by
    intro h
    apply hgO
    intro a ha
    have h1 : f ⟨a, hAH ha⟩ = 1 := by
      have : f ⟨a, hAH ha⟩ ∈ E := ⟨⟨a, hAH ha⟩, ha, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    have h2 : (⟨a, hAH ha⟩ : ↥H) ∈ O := by
      rw [← hfker]
      exact h1
    rw [hOsub] at h2
    exact h2
  have hVcl : conjClosure V T = V :=
    le_antisymm (conjClosure_le fun _ ht _ hz => (Subgroup.mem_normalizer_iff.mp (hTV ht) _).mp hz)
      (le_conjClosure V T)
  obtain ⟨-, -, hOLT⟩ := h3228 G T L V hy.fsu
  rw [hy.conjClosure_eq, hVcl] at hOLT
  have hL1L : L1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hHMN : H ⊓ M ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← hL1T, ← hOLT]
    exact (sup_le_sup_right hL1L T).trans (le_normalizer_pCoreOf 2 (L ⊔ T))
  have hAP : A ≤ pCoreOf 2 (H ⊓ M) := hgT.trans (le_pCoreOf_of_le_normalizer 2
    (inf_le_left.trans (le_inf hTH hTM)) hHMN (hy.sylow.1.to_le inf_le_left))
  have hTHM : IsSylowIn 2 T (H ⊓ M) :=
    ⟨le_inf hTH hTM, hy.sylow.1,
      fun h => hy.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le (le_inf hTH hTM)))⟩
  have hPT : pCoreOf 2 (H ⊓ M) ≤ T := hTHM.le_of_normal (pCoreOf_le 2 _)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).2
      (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hNM : ∀ x : ↥H, f x ∈ Subgroup.normalizer ((S ⊓ K : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) →
      (x : G) ∈ M := by
    set X := ((Subgroup.normalizer ((S ⊓ K : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O))).comap f).map
      H.subtype with hX
    have hXH : X ≤ H := Subgroup.map_subtype_le _
    have hTX : T ≤ X := fun t ht => ⟨⟨t, hTH ht⟩,
      le_normalizer_inf_normal (K := K) ⟨⟨t, hTH ht⟩, ht, rfl⟩, rfl⟩
    have hXinH : InH T X := by
      refine ⟨hTX, fun hbot => hHs.1.2 ?_⟩
      have hle := le_pCoreOf_of_le_normalizer 2 (hOT.trans hTX)
        (hXH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
      rw [hbot] at hle
      exact le_bot_iff.1 hle
    have hXne : X ≠ H := by
      intro hXeq
      have hall : ∀ w : ↥H ⧸ O,
          w ∈ Subgroup.normalizer ((S ⊓ K : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) := by
        intro w
        obtain ⟨x, rfl⟩ := hfs w
        have hx : (x : G) ∈ X := by rw [hXeq]; exact x.2
        obtain ⟨x', hx', hxx'⟩ := hx
        rw [show x = x' from Subtype.ext hxx'.symm]
        exact hx'
      have hn : (S ⊓ K).Normal :=
        Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 fun w _ => hall w)
      have hnK : ((S ⊓ K).subgroupOf K).Normal := hn.subgroupOf K
      have := hKs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S ⊓ K).subgroupOf K) with h | h
      · have hbot : S ⊓ K = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          have hxK : x ∈ K := (Subgroup.mem_inf.1 hx).2
          have : (⟨x, hxK⟩ : ↥K) ∈ (S ⊓ K).subgroupOf K := hx
          rw [h, Subgroup.mem_bot] at this
          exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
        have hi := hSK.2.2
        rw [hbot, Subgroup.relIndex_bot_left, h20160] at hi
        exact hi (by norm_num)
      · have hK2 : IsPGroup 2 ↥K := by
          intro k
          have hk : k ∈ (S ⊓ K).subgroupOf K := by rw [h]; exact Subgroup.mem_top k
          obtain ⟨n, hn⟩ := hSsyl.2.1 ⟨(k : ↥H ⧸ O), (Subgroup.mem_inf.1 hk).1⟩
          exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hK2
        rw [h20160] at hn
        have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 20160)
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
    have hXM : X ≤ M := by
      by_contra hXM
      exact hXne (hHs.2.2 X hXinH hXH hXM)
    intro x hx
    exact hXM ⟨x, hx, rfl⟩
  have hB : ∀ x ∈ E, ∀ d ∈ K,
      d ∈ Subgroup.normalizer ((S ⊓ K : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) →
        x * d * x⁻¹ * d⁻¹ ∈ S := by
    rintro _ ⟨a, ha, rfl⟩ d - hdN
    obtain ⟨h, rfl⟩ := hfs d
    have hhHM : (h : G) ∈ H ⊓ M := Subgroup.mem_inf.2 ⟨h.2, hNM h hdN⟩
    have haP : (a : G) ∈ pCoreOf 2 (H ⊓ M) := hAP ha
    have hc : (a : G) * h * (a : G)⁻¹ * (h : G)⁻¹ ∈ T := by
      apply hPT
      have h1 : (h : G) * (a : G)⁻¹ * (h : G)⁻¹ ∈ pCoreOf 2 (H ⊓ M) :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hhHM) _).1
          ((pCoreOf 2 (H ⊓ M)).inv_mem haP)
      have := (pCoreOf 2 (H ⊓ M)).mul_mem haP h1
      simpa [mul_assoc] using this
    refine ⟨a * h * a⁻¹ * h⁻¹, ?_, ?_⟩
    · show ((a * h * a⁻¹ * h⁻¹ : ↥H) : G) ∈ T
      simpa using hc
    · simp only [map_mul, map_inv]
  obtain ⟨y, Y₁, hgood⟩ := exists_goodPair hSsyl hpar hout hES hEe hE1 hB
  obtain ⟨h₀, rfl⟩ := hfs y
  obtain ⟨hE'S, hE'Y₁, hCY₁, hSY₁, hPSL, hE'O⟩ := hgood
  set g' := g * (h₀ : G)⁻¹ with hg'
  have hA'eq : conjSubgroup V g' = A.map (MulAut.conj (h₀ : G)).toMonoidHom := by
    rw [hg', ← conjSubgroup_conjSubgroup, ← hAdef, conjSubgroup_inv_eq_map]
  have hA'H : conjSubgroup V g' ≤ H := by
    rw [hA'eq]
    rintro _ ⟨a, ha, rfl⟩
    exact H.mul_mem (H.mul_mem h₀.2 (hAH ha)) (H.inv_mem h₀.2)
  have hE' : ((conjSubgroup V g').subgroupOf H).map f =
      E.map (MulAut.conj (f h₀)).toMonoidHom := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ conjSubgroup V g' := hx
      rw [hA'eq] at hx'
      obtain ⟨a, ha, hax⟩ := hx'
      refine ⟨f ⟨a, hAH ha⟩, ⟨⟨a, hAH ha⟩, ha, rfl⟩, ?_⟩
      have hx' : x = h₀ * ⟨a, hAH ha⟩ * h₀⁻¹ := Subtype.ext (by rw [← hax]; rfl)
      rw [hx']
      simp [MulAut.conj_apply]
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨h₀ * a * h₀⁻¹, ?_, ?_⟩
      · show ((h₀ * a * h₀⁻¹ : ↥H) : G) ∈ conjSubgroup V g'
        rw [hA'eq]
        exact ⟨a, ha, rfl⟩
      · simp [MulAut.conj_apply]
  have hfA' : ∀ a ∈ conjSubgroup V g', ∀ ha : a ∈ H,
      f ⟨a, ha⟩ ∈ E.map (MulAut.conj (f h₀)).toMonoidHom := fun a haA ha => by
    rw [← hE']
    exact ⟨⟨a, ha⟩, haA, rfl⟩
  set H₁ := (Y₁.comap f).map H.subtype with hH₁
  have hH₁H : H₁ ≤ H := Subgroup.map_subtype_le _
  have hmemH₁ : ∀ x : ↥H, (x : G) ∈ H₁ ↔ f x ∈ Y₁ := fun x => by
    constructor
    · rintro ⟨x', hx', hxx'⟩
      rw [show x = x' from Subtype.ext hxx'.symm]
      exact hx'
    · intro hx
      exact ⟨x, hx, rfl⟩
  set ρ : ↥H₁ →* ↥Y₁ := (f.comp (Subgroup.inclusion hH₁H)).codRestrict Y₁
    (fun x => (hmemH₁ ⟨x, hH₁H x.2⟩).1 x.2) with hρ
  have hρapp : ∀ x : ↥H₁, ((ρ x : ↥Y₁) : ↥H ⧸ O) = f ⟨x, hH₁H x.2⟩ := fun _ => rfl
  have hρs : Function.Surjective ρ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := hfs w
    exact ⟨⟨x, (hmemH₁ x).2 hw⟩, Subtype.ext rfl⟩
  have hρk : IsPGroup 2 ρ.ker := by
    intro x
    have hx1 : f ⟨(x : ↥H₁), hH₁H (x : ↥H₁).2⟩ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
      rw [hρapp] at this
      exact this
    have hxO : (⟨(x : ↥H₁), hH₁H (x : ↥H₁).2⟩ : ↥H) ∈ O := (QuotientGroup.eq_one_iff _).1 hx1
    obtain ⟨n, hn⟩ := hO2 ⟨_, hxO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun u : ↥O => ((u : ↥H) : G)) hn
    simpa using this
  refine ⟨g', H₁, hH₁H, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hfa := hE'S (hfA' a ha (hA'H ha))
    have : (⟨a, hA'H ha⟩ : ↥H) ∈ S.comap f := hfa
    rw [hTcomap] at this
    exact this
  ·
    exact (hmemH₁ ⟨a, hA'H ha⟩).2 (hE'Y₁ (hfA' a ha (hA'H ha)))
  ·
    have hcT : (T ⊓ H₁).subgroupOf H = (S ⊓ Y₁).comap f := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf,
        hmemH₁]
      constructor
      · rintro ⟨hxT, hxY⟩
        exact ⟨⟨x, hxT, rfl⟩, hxY⟩
      · rintro ⟨hxS, hxY⟩
        refine ⟨?_, hxY⟩
        have : x ∈ S.comap f := hxS
        rw [hTcomap] at this
        exact this
    have hcH₁ : H₁.subgroupOf H = Y₁.comap f := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hmemH₁]
    rw [← E1.isSylowIn_subgroupOf_iff (inf_le_left.trans hTH) hH₁H, hcT, hcH₁]
    refine ⟨Subgroup.comap_mono inf_le_right,
      hSY₁.2.1.comap_of_ker_isPGroup f (by rw [hfker]; exact hO2), ?_⟩
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hfs]
    exact hSY₁.2.2
  ·
    rintro t ⟨htT, -, htc⟩
    have htH := hTH htT
    refine (hmemH₁ ⟨t, htH⟩).2 (hCY₁ (Subgroup.mem_inf.2 ⟨⟨⟨t, htH⟩, htT, rfl⟩, ?_⟩))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [← hE'] at hw
    obtain ⟨⟨a, haH⟩, haA, rfl⟩ := hw
    have hc := htc a haA
    have h1 : f ⁅(⟨t, htH⟩ : ↥H), ⟨a, haH⟩⁆ = 1 := by
      rw [← MonoidHom.mem_ker, hfker, hOsub, Subgroup.mem_subgroupOf]
      exact hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  ·
    obtain ⟨e⟩ := nonempty_quot_pCore_equiv hρs hρk
    exact isPSL_oTwoUpper_of_equiv e hPSL
  ·
    intro hle
    apply hE'O
    intro w hw
    rw [← hE'] at hw
    obtain ⟨⟨a, haH⟩, haA, rfl⟩ := hw
    obtain ⟨u, hu, hua⟩ := hle haA
    have hρu : ρ u ∈ CFSG.Open.pCore 2 ↥Y₁ := map_pCore_le 2 ρ hρs ⟨u, hu, rfl⟩
    refine ⟨ρ u, hρu, ?_⟩
    rw [Subgroup.coe_subtype, hρapp]
    congr 1
    exact Subtype.ext hua

end CFSG.Quasithin.H13
