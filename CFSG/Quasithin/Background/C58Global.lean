module

public import CFSG.Quasithin.Background.C58Gamma
public import CFSG.Quasithin.Background.C58Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.C58IndexTwo

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_mul_odd [Finite G] {S N : Subgroup G} (hS : IsSylowTwoOf S N)
    (hSn : N ≤ normalizer (S : Set G)) {g : G} (hg : g ∈ N) :
    ∃ a ∈ S, ∃ b ∈ N, Odd (orderOf b) ∧ g = a * b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : (S.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hS.1).mpr hSn
  have hK2 : IsPGroup 2 (S.subgroupOf N) := A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1
  have hidx : ¬ 2 ∣ (S.subgroupOf N).index := hS.2.2
  have hcop : Nat.Coprime (Nat.card (S.subgroupOf N)) (S.subgroupOf N).index := by
    obtain ⟨k, hk⟩ := hK2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  obtain ⟨Hc, hHc⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  obtain ⟨⟨k, h⟩, hkh, -⟩ := hHc.existsUnique ⟨g, hg⟩
  have hcardHc : Nat.card Hc = (S.subgroupOf N).index := by
    have h1 := hHc.card_mul_card
    have h2 := Subgroup.card_mul_index (S.subgroupOf N)
    have hpos : 0 < Nat.card (S.subgroupOf N) := Nat.card_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  refine ⟨((k : S.subgroupOf N) : N), k.2, ((h : Hc) : N), ((h : Hc) : N).2, ?_, ?_⟩
  · have h1 : orderOf (((h : Hc) : N) : G) = orderOf (h : Hc) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [h1]
    have h2 : orderOf (h : Hc) ∣ Nat.card Hc := orderOf_dvd_natCard h
    rw [hcardHc] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun hd => hidx (hd.trans h2))
  · have := congrArg Subtype.val hkh
    simpa using this.symm

namespace GammaSetup

variable {H T R K₁ : Subgroup G} {t x : G} (hs : GammaSetup H T R K₁ t x)
include hs

theorem isSylowTwoOf_Y [Finite G] :
    IsSylowTwoOf T (normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G)) := by
  have hT : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hs.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]; exact hs.sylow.2
  exact isSylowTwoOf_of_le hT hs.le_normalizer_T₁

theorem false_of_input [Finite G] (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : quasithinIsQTKECat G) (hG64 : InputC512G64) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hs.isA4
  set U₁ := blockU K₁ with hU₁
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set Y := normalizer (T₁ : Set G) with hY
  have hT2 : IsPGroup 2 T := hs.sylow.1
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  have hTY : IsSylowTwoOf T Y := hs.isSylowTwoOf_Y
  have hidx₁ : T₁.relIndex T = 2 := hs.relIndex_T₁
  have hT₁T : T₁ ≤ T := inf_le_left
  have hT₁Y : T₁ ≤ Y := Subgroup.le_normalizer
  have htY : t ∈ Y := hs.le_normalizer_T₁ hs.tT
  have hxY : x ∈ Y := hs.xN
  have htT₁ : t ∉ T₁ := fun h => hs.tK h.2
  have hUT₁ : U₁ ≤ T₁ := hs.U_le_T₁
  have hT₁U : T₁ ≤ normalizer (U₁ : Set G) := hs.T₁_le_normalizer_U
  have hT₁K : T₁ ≤ normalizer (K₁ : Set G) := inf_le_right
  obtain ⟨N₁, hN₁Y, hYN₁, hT₁N₁, hidxN₁, hsylN₁⟩ := exists_index_two hTY hT₁T hidx₁ le_rfl
  have hN₁T₁ : N₁ ≤ normalizer (T₁ : Set G) := hN₁Y
  have hN₁c : ∀ g ∈ N₁, conjSubgroup U₁ g ≤ centralizer (U₁ : Set G) := by
    intro g hg
    obtain ⟨a, haT₁, b, hbN₁, hbodd, rfl⟩ := exists_mul_odd hsylN₁ hN₁T₁ hg
    rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr (hT₁U haT₁)]
    exact hs.conj_le_of_odd (hN₁Y hbN₁) hbodd
  have hxN₁ : x ∉ N₁ := fun h => hs.xU (hN₁c x h)
  have htN₁ : t ∉ N₁ := by
    intro htN
    have h1 : zpowers t ≤ T₁ :=
      le_of_isPGroup_of_normal hsylN₁ hN₁T₁ (zpowers_le.mpr htN)
        (hT2.to_le (zpowers_le.mpr hs.tT))
    exact htT₁ (h1 (mem_zpowers t))
  have hidxY : (N₁.subgroupOf Y).index = 2 := hidxN₁
  have hmulN₁ : ∀ a ∈ Y, ∀ b ∈ Y, (a * b ∈ N₁ ↔ (a ∈ N₁ ↔ b ∈ N₁)) := by
    intro a ha b hb
    have := Subgroup.mul_mem_iff_of_index_two hidxY (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa [mem_subgroupOf] using this
  have hxtN₁ : x * t ∈ N₁ := (hmulN₁ x hxY t htY).mpr (iff_of_false hxN₁ htN₁)
  obtain ⟨W, hP⟩ := hs.pairData
  obtain ⟨hUB, hBK, hBnt⟩ := hs.baum_facts
  set B := baum T₁ with hB
  set Q := B ⊓ centralizer (U₁ : Set G) with hQ
  set D := Q ⊓ centralizer (K₁ : Set G) with hD
  have hBT₁ : B ≤ T₁ := inf_le_left
  have hYB : Y ≤ normalizer (B : Set G) := normalizer_le_normalizer_baum T₁
  set V := conjClosure U₁ N₁ with hV
  have hUV : U₁ ≤ V := le_conjClosure U₁ N₁
  have hN₁V : N₁ ≤ normalizer (V : Set G) := le_normalizer_conjClosure U₁ N₁
  have hconjV : ∀ g ∈ N₁, conjSubgroup U₁ g ≤ V := by
    intro g hg v hv
    rw [mem_conjSubgroup_iff] at hv
    have := mem_conjClosure (inv_mem hg) hv
    simpa [mul_assoc] using this
  have hVQ : V ≤ Q := by
    refine conjClosure_le fun n hn u hu => ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hYB (hN₁Y hn)) u).mp (hUB hu)
    · have h1 := hN₁c n⁻¹ (inv_mem hn)
      exact h1 (mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hu))
  have hVT₁ : V ≤ T₁ := hVQ.trans (inf_le_left.trans hBT₁)
  have hVC : V ≤ centralizer (U₁ : Set G) := hVQ.trans inf_le_right
  have hVV : V ≤ centralizer (V : Set G) := by
    have hgen : ∀ n ∈ N₁, V ≤ centralizer ((conjSubgroup U₁ n : Subgroup G) : Set G) := by
      intro n hn
      have h1 := (le_centralizer_iff_conj n).mp hVC
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (hN₁V hn)] at h1
    intro v hv
    show v ∈ centralizer ((Subgroup.closure {x | ∃ h ∈ N₁, ∃ z ∈ U₁, h * z * h⁻¹ = x} :
      Subgroup G) : Set G)
    rw [Subgroup.centralizer_closure, mem_centralizer_iff]
    rintro _ ⟨n, hn, u, hu, rfl⟩
    have h1 := hgen n⁻¹ (inv_mem hn) hv
    rw [mem_centralizer_iff] at h1
    exact h1 _ (mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hu))
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    ((mem_centralizer_iff.mp (hVV hb)) a ha)
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨n, -, u, hu, rfl⟩ := hy
      have h1 := hA.sq_U u hu
      have : (n * u * n⁻¹) ^ 2 = n * u ^ 2 * n⁻¹ := by simp only [pow_two]; group
      rw [this, h1]; simp
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab := hVcomm a ha b hb
      have : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
        simp only [pow_two]
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = a * a * (b * b) := by group
      rw [this, iha, ihb, one_mul]
    | inv a ha iha =>
      rw [inv_pow, iha, inv_one]
  have hVe : IsElemAbelian 2 V := isElemAbelian_two_iff.mpr ⟨hVcomm, hVsq⟩
  have hV2 : IsPGroup 2 V := hT₁2.to_le hVT₁
  have hKV : K₁ ≤ normalizer (V : Set G) := by
    have key : ∀ k ∈ K₁, ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
      intro k hk v hv
      obtain ⟨u, hu, d, hd, rfl⟩ := hP.mem_UD (hVQ hv)
      have hdk : k * d = d * k := (mem_centralizer_iff.mp hd.2) k hk
      have hku : k * u * k⁻¹ ∈ U₁ :=
        (mem_normalizer_iff.mp (IsA4Block.le_normalizer_U hA hk) u).mp hu
      have hkd : k * d * k⁻¹ = d := by rw [hdk]; group
      have e : k * (u * d) * k⁻¹ = (k * u * k⁻¹ * u⁻¹) * (u * d) := by
        calc k * (u * d) * k⁻¹ = (k * u * k⁻¹) * (k * d * k⁻¹) := by group
          _ = (k * u * k⁻¹) * d := by rw [hkd]
          _ = (k * u * k⁻¹ * u⁻¹) * (u * d) := by group
      rw [e]
      exact mul_mem (hUV (mul_mem hku (inv_mem hu))) hv
    intro k hk
    exact B6.mem_normalizer_of_forall_mem (fun v hv => key k hk v hv)
      (fun v hv => by simpa using key k⁻¹ (inv_mem hk) v hv)
  set X := N₁ ⊔ K₁ with hX
  have hXV : X ≤ normalizer (V : Set G) := sup_le hN₁V hKV
  have hN₁X : N₁ ≤ X := le_sup_left
  have hKX : K₁ ≤ X := le_sup_right
  have hT₁X : T₁ ≤ X := hT₁N₁.trans hN₁X
  have hT₁N : T₁ ≤ normalizer (V : Set G) := hT₁N₁.trans hN₁V
  have hWc := hP.rank1.commutator_conj hP.hx hP.hx1 hP.hx2
  have hWU : W ≤ U₁ := hP.rank1.W_le_U
  have hWcard : Nat.card W = 2 := by
    have h1 := card_eq_card_mul_relIndex hWU
    rw [hP.rank1.idx_W, hA.card_U] at h1
    omega
  obtain ⟨e, heU, he1, heT₁⟩ := hs.exists_central
  obtain ⟨y, hyB, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hBnt
  have hyQ : y ∉ Q := fun h => hyC h.2
  have heW : e ∈ W := (hP.rank1.cent_y y hyB hyQ e heU).mpr (heT₁ y (hBT₁ hyB)).symm
  have he2 : e ^ 2 = 1 := hA.sq_U e heU
  have hWe : W = zpowers e := by
    have hle : zpowers e ≤ W := zpowers_le.mpr heW
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hWcard, Nat.card_zpowers, orderOf_eq_prime he2 he1]
  have heT₁' : e ∈ T₁ := hUT₁ heU
  have hWZ : W ≤ quasithinOmegaOneCenter T₁ := by
    rw [hWe, zpowers_le]
    refine mem_quasithinOmegaOneCenter_iff.mpr ⟨heT₁', ?_, he2⟩
    rw [mem_centralizer_iff]
    intro g hg; exact heT₁ g hg
  have hUtT₁ : conjSubgroup U₁ t ≤ T₁ := by
    have h1 := conjSubgroup_mono hUT₁ t
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (hs.le_normalizer_T₁ hs.tT)] at h1
  have hWtV : conjSubgroup W t ≤ V := by
    rw [← hWc.1, C5.conjSubgroup_commutator, conjSubgroup_conjSubgroup]
    refine (Subgroup.commutator_mono le_rfl (hconjV _ hxtN₁)).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : a * b * a⁻¹ ∈ V := (mem_normalizer_iff.mp (hT₁N (hUtT₁ ha)) b).mp hb
    simpa [commutatorElement_def] using mul_mem h1 (inv_mem hb)
  have hzV : e * (t⁻¹ * e * t) ∈ V := by
    refine mul_mem (hUV heU) (hWtV ?_)
    rw [mem_conjSubgroup_iff]
    have : t * (t⁻¹ * e * t) * t⁻¹ = e := by group
    rw [this]; exact heW
  obtain ⟨hzZ, hz1⟩ := hs.z_mem heU he1 heT₁
  have hTtop : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT2, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]; exact hs.sylow.2
  have hVZ : V ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
    intro h
    have hz : e * (t⁻¹ * e * t) ∈ V ⊓ (T ⊓ centralizer (T : Set G)) := by
      obtain ⟨h1, h2, -⟩ := mem_quasithinOmegaOneCenter_iff.mp hzZ
      exact ⟨hzV, h1, h2⟩
    rw [h] at hz
    exact hz1 hz
  have hNVc : CharTwo (normalizer (V : Set G)) :=
    CT.charTwo_normalizer_of_inf_center hs.even hTtop hV2 hVZ
  obtain ⟨S', hS', hT₁S'⟩ := A4.exists_isSylowTwoOf_ge (hT₁N₁.trans hN₁V) hT₁2
  have hS'card : Nat.card S' ≤ Nat.card T := by
    obtain ⟨P, hP'⟩ := hS'.2.1.exists_le_sylow
    have h1 : Nat.card S' ≤ Nat.card P := Subgroup.card_le_of_le hP'
    have h2 : Nat.card P = Nat.card (hT2.toSylow hs.sylow.2) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    exact h1.trans h2.le
  have hXc : CharTwo X := by
    refine charTwo_of_relIndex_le_two hNVc hS' hXV ?_
    have h1 : X.relIndex S' ∣ T₁.relIndex S' := Subgroup.relIndex_dvd_of_le_left S' hT₁X
    have h2 : T₁.relIndex S' ≤ 2 := by
      have e1 := card_eq_card_mul_relIndex hT₁S'
      have e2 := card_eq_card_mul_relIndex hT₁T
      rw [hidx₁] at e2
      have hpos : 0 < Nat.card T₁ := Nat.card_pos
      have : Nat.card T₁ * T₁.relIndex S' ≤ Nat.card T₁ * 2 := by
        rw [← e1, ← e2]; exact hS'card
      exact Nat.le_of_mul_le_mul_left this hpos
    have h0 : T₁.relIndex S' ≠ 0 := Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf S')
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h1).trans h2
  have hsylX : IsSylowTwoOf T₁ X := by
    obtain ⟨S'', hS'', hT₁S''⟩ := A4.exists_isSylowTwoOf_ge hT₁X hT₁2
    by_cases heq : T₁ = S''
    · rw [heq]; exact hS''
    exfalso
    have hlt : T₁.subgroupOf S'' < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => heq ?_
      exact le_antisymm hT₁S'' fun g hg => by
        have : (⟨g, hg⟩ : S'') ∈ T₁.subgroupOf S'' := htop ▸ trivial
        exact this
    have : Group.IsNilpotent S'' := hS''.2.1.isNilpotent
    have hlt' := Group.normalizerCondition_of_isNilpotent _ hlt
    obtain ⟨g, hgN, hgT⟩ := IsConcreteLE.exists_of_lt hlt'
    have hgY : (g : G) ∈ Y := by
      refine B6.mem_normalizer_of_forall_mem (fun a ha => ?_) (fun a ha => ?_)
      · have := (mem_normalizer_iff.mp hgN ⟨a, hT₁S'' ha⟩).mp (by simpa [mem_subgroupOf] using ha)
        simpa [mem_subgroupOf] using this
      · have := (mem_normalizer_iff.mp (inv_mem hgN) ⟨a, hT₁S'' ha⟩).mp
          (by simpa [mem_subgroupOf] using ha)
        simpa [mem_subgroupOf] using this
    have hgT₁ : (g : G) ∉ T₁ := fun h => hgT (by simpa [mem_subgroupOf] using h)
    have hgN₁ : (g : G) ∉ N₁ := by
      intro h
      have h1 : zpowers (g : G) ≤ T₁ :=
        le_of_isPGroup_of_normal hsylN₁ hN₁T₁ (zpowers_le.mpr h)
          (hS''.2.1.to_le (zpowers_le.mpr g.2))
      exact hgT₁ (h1 (mem_zpowers _))
    have hgN₁' : (g : G)⁻¹ ∉ N₁ := fun h => hgN₁ (by simpa using inv_mem h)
    have hxg : x * (g : G)⁻¹ ∈ N₁ :=
      (hmulN₁ x hxY _ (inv_mem hgY)).mpr (iff_of_false hxN₁ hgN₁')
    have hxX : x ∈ X := by
      have : x = (x * (g : G)⁻¹) * g := by group
      rw [this]
      exact mul_mem (hN₁X hxg) (hS''.1 g.2)
    apply hs.xU
    intro v hv
    rw [mem_conjSubgroup_iff] at hv
    have hv' : v ∈ V := by
      have := (mem_normalizer_iff.mp (hXV (inv_mem hxX)) _).mp (hUV hv)
      simpa [mul_assoc] using this
    rw [mem_centralizer_iff]
    intro u hu
    exact hVcomm u (hUV hu) v hv'
  obtain ⟨c, hcK, hc3, hcN, hcfp, hKc⟩ := hA.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨a, haUx, hna⟩ := IsConcreteLE.not_le_iff_exists.mp hs.xU
  have hUxT₁ : conjSubgroup U₁ x ≤ T₁ := by
    have h1 := conjSubgroup_mono hUT₁ x
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hxY] at h1
  have haT₁ : a ∈ T₁ := hUxT₁ haUx
  have ha2 : a ^ 2 = 1 := by
    rw [mem_conjSubgroup_iff] at haUx
    have h1 := hA.sq_U _ haUx
    have h2 : x * a ^ 2 * x⁻¹ = (x * a * x⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
    have h3 : x * a ^ 2 * x⁻¹ = 1 := by rw [h2, h1]
    calc a ^ 2 = x⁻¹ * (x * a ^ 2 * x⁻¹) * x := by group
      _ = 1 := by rw [h3]; group
  have hVa : ⁅V, zpowers a⁆ = W := by
    have hle : ⁅V, zpowers a⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro v hv g hg
      have hg' : g ∈ conjSubgroup U₁ x := (zpowers_le.mpr haUx) hg
      obtain ⟨u, hu, d, hd, rfl⟩ := hP.mem_UD (hVQ hv)
      have hdg : g * d = d * g := hP.hDUx g hg' d hd
      have e : ⁅u * d, g⁆ = ⁅u, g⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc u * d * g * (u * d)⁻¹ * g⁻¹ = u * (d * g) * d⁻¹ * u⁻¹ * g⁻¹ := by group
          _ = u * (g * d) * d⁻¹ * u⁻¹ * g⁻¹ := by rw [hdg]
          _ = u * g * u⁻¹ * g⁻¹ := by group
      rw [e, ← hWc.1]
      exact Subgroup.commutator_mem_commutator hu hg'
    have hne : ⁅V, zpowers a⁆ ≠ ⊥ := by
      intro h
      apply hna
      rw [mem_centralizer_iff]
      intro u hu
      have h1 : ⁅u, a⁆ ∈ ⁅V, zpowers a⁆ :=
        Subgroup.commutator_mem_commutator (hUV hu) (mem_zpowers a)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have h2 : 1 < Nat.card ↥⁅V, zpowers a⁆ := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hWcard]; omega)
  have hVW : conjClosure W X = V := by
    apply le_antisymm
    · exact conjClosure_le fun g hg w hw => (mem_normalizer_iff.mp (hXV hg) w).mp (hUV (hWU hw))
    · have hUC : U₁ ≤ conjClosure W X :=
        hA.le_of_mem (hKX.trans (le_normalizer_conjClosure W X)) (le_conjClosure W X heW) heU he1
      exact conjClosure_le fun n hn u hu =>
        (mem_normalizer_iff.mp (le_normalizer_conjClosure W X (hN₁X hn)) u).mp (hUC hu)
  have hred : IsTwoReducedIn X V := by
    rw [← hVW]
    exact isTwoReducedIn_conjClosure_of_sylowIn hsylX.1 hsylX.2.1 hsylX.2.2 hXc hWZ
  have hO2 : pCoreOf 2 X ≠ ⊥ := by
    intro h
    have hcC : c ∈ centralizer (pCoreOf 2 X : Set G) := by
      rw [h, mem_centralizer_iff]
      intro g hg
      rw [(mem_bot.mp hg), one_mul, mul_one]
    have hc : c ∈ pCoreOf 2 X := hXc ⟨hKX hcK, hcC⟩
    rw [h, mem_bot] at hc
    rw [hc, orderOf_one] at hc3
    norm_num at hc3
  have hcV : c ∉ centralizer (V : Set G) := by
    intro h
    apply hcfp e heU he1
    have h1 : e * c = c * e := (mem_centralizer_iff.mp h) e (hUV heU)
    calc c * e * c⁻¹ = e * c * c⁻¹ := by rw [h1]
      _ = e := by group
  have hac : a * c * a⁻¹ * c ∈ centralizer (V : Set G) := by
    have haB : a ∈ B := hP.rank1.conj_le_B hP.hx haUx
    exact hVV (hUV (IsA4Block.mul_conj_mem hA ha2 (hBK haB) (hP.rank1.B_le_normU haB) hna hcK))
  have hT₁c : T₁ ≤ normalizer
      ((zpowers c ⊔ X ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
    have heq : zpowers c ⊔ X ⊓ centralizer (V : Set G) = K₁ ⊔ X ⊓ centralizer (V : Set G) := by
      apply le_antisymm
      · exact sup_le_sup_right (zpowers_le.mpr hcK) _
      · refine sup_le (hKc.le.trans (sup_le ?_ le_sup_left)) le_sup_right
        exact (le_inf (hUT₁.trans hT₁X) (hUV.trans hVV)).trans le_sup_right
    rw [heq]
    intro g hg
    exact C1.mem_normalizer_sup (hT₁K hg)
      (mem_normalizer_inf ((hT₁X.trans Subgroup.le_normalizer) hg)
        (mem_normalizer_centralizer (hT₁N hg)))
  have hXeq : X = X ⊓ normalizer (T₁ : Set G) ⊔ zpowers c := by
    apply le_antisymm
    · refine sup_le ((le_inf hN₁X hN₁Y).trans le_sup_left) ?_
      refine hKc.le.trans (sup_le ?_ le_sup_right)
      exact (le_inf (hUT₁.trans hT₁X) (hUT₁.trans hT₁Y)).trans le_sup_left
    · exact sup_le inf_le_left (zpowers_le.mpr (hKX hcK))
  have hconc := hG64 G hsimple hnonab hqtke X V T₁ a c hO2 hred hsylX haT₁ ha2
    (by rw [hVa, hWcard]) (by rw [hVa, hVW]) (hKX hcK) hc3' hcV hac hT₁c hXeq
  have hVc : ⁅V, zpowers c⁆ = U₁ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro v hv g hg
      obtain ⟨u, hu, d, hd, rfl⟩ := hP.mem_UD (hVQ hv)
      have hgK : g ∈ K₁ := (zpowers_le.mpr hcK) hg
      have hdg : g * d = d * g := (mem_centralizer_iff.mp hd.2) g hgK
      have e : ⁅u * d, g⁆ = u * (g * u⁻¹ * g⁻¹) := by
        rw [commutatorElement_def]
        calc u * d * g * (u * d)⁻¹ * g⁻¹ = u * (d * g) * d⁻¹ * u⁻¹ * g⁻¹ := by group
          _ = u * (g * d) * d⁻¹ * u⁻¹ * g⁻¹ := by rw [hdg]
          _ = u * (g * u⁻¹ * g⁻¹) := by group
      rw [e]
      exact mul_mem hu
        ((mem_normalizer_iff.mp (IsA4Block.le_normalizer_U hA hgK) _).mp (inv_mem hu))
    · intro w hw
      have hmem : ∀ u ∈ U₁, u * (c * u⁻¹ * c⁻¹) ∈ U₁ := fun u hu =>
        mul_mem hu ((mem_normalizer_iff.mp hcN _).mp (inv_mem hu))
      let f : U₁ → U₁ := fun u => ⟨u * (c * (u : G)⁻¹ * c⁻¹), hmem u u.2⟩
      have hf : Function.Injective f := by
        intro u u' huu'
        have h1 : (u : G) * (c * (u : G)⁻¹ * c⁻¹) = u' * (c * (u' : G)⁻¹ * c⁻¹) :=
          congrArg Subtype.val huu'
        by_contra hne
        have hw1 : (u' : G)⁻¹ * u ≠ 1 := fun h => hne (Subtype.ext (by
          have := congrArg ((u' : G) * ·) h
          simpa using this))
        apply hcfp ((u' : G)⁻¹ * u) (mul_mem (inv_mem u'.2) u.2) hw1
        have h2 : c * (u' : G)⁻¹ * c⁻¹ = (u' : G)⁻¹ * u * (c * (u : G)⁻¹ * c⁻¹) := by
          calc c * (u' : G)⁻¹ * c⁻¹ = (u' : G)⁻¹ * (u' * (c * (u' : G)⁻¹ * c⁻¹)) := by group
            _ = (u' : G)⁻¹ * ((u : G) * (c * (u : G)⁻¹ * c⁻¹)) := by rw [h1]
            _ = (u' : G)⁻¹ * u * (c * (u : G)⁻¹ * c⁻¹) := by group
        calc c * ((u' : G)⁻¹ * u) * c⁻¹ = (c * (u' : G)⁻¹ * c⁻¹) * (c * u * c⁻¹) := by group
          _ = (u' : G)⁻¹ * u := by rw [h2]; group
      obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
      have h1 : (u : G) * (c * (u : G)⁻¹ * c⁻¹) = w := congrArg Subtype.val hu
      rw [← h1]
      have e : (u : G) * (c * (u : G)⁻¹ * c⁻¹) = ⁅(u : G), c⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hUV u.2) (mem_zpowers c)
  have hN₁U : N₁ ≤ normalizer (U₁ : Set G) := by
    rw [← hVc]; exact (le_inf hN₁X hN₁Y).trans hconc
  have hxt : x * t ∈ normalizer (U₁ : Set G) := hN₁U hxtN₁
  have hperm : ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ t⁻¹, a * b = b * a := by
    rcases hs.cfg.perm t⁻¹ (inv_mem hs.tT) with h | h
    · exact (hs.tK (by simpa using inv_mem (conjSubgroup_eq_iff_mem_normalizer.mp h))).elim
    · exact h
  apply hs.xU
  have e : conjSubgroup U₁ x = conjSubgroup U₁ t⁻¹ := by
    rw [show x = x * t * t⁻¹ by group, ← conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.mpr hxt]
  rw [e]
  intro v hv
  rw [mem_centralizer_iff]
  intro u hu
  exact hperm u (hA.le hu) v (conjSubgroup_mono hA.le t⁻¹ hv)

end GammaSetup

end CFSG.Quasithin.C58
