module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1543Unique
public import CFSG.Quasithin.Background.D2Thirteen
import CFSG.Quasithin.Background.A4Reduced
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1542FourModule

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

section Sections

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_pCoreOf_of_relIndex {X : Subgroup G} {p : ℕ}
    (hXp : (pCoreOf 2 X).relIndex X = p) {x : G} (hx : x ∈ X) : x ^ p ∈ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have : ((pCoreOf 2 X).subgroupOf X).Normal := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hcard : Nat.card (X ⧸ (pCoreOf 2 X).subgroupOf X) = p := by
    rw [← Subgroup.index_eq_card]
    exact hXp
  have h1 : (⟨x, hx⟩ : X) ^ p ∈ (pCoreOf 2 X).subgroupOf X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'
  exact Subgroup.mem_subgroupOf.mp h1

theorem eq_bot_of_le_centralizer_of_pow {Γ : Type*} [Group Γ] [Finite Γ] {Y P A : Subgroup Γ}
    (hO2 : pCoreOf 2 Y = ⊥) (hPn : Y ≤ Subgroup.normalizer (P : Set Γ))
    (hY2 : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ P) (hAY : A ≤ Y) (hA2 : IsPGroup 2 A)
    (hAP : A ≤ Subgroup.centralizer (P : Set Γ)) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cc := Y ⊓ Subgroup.centralizer (P : Set Γ) with hCc
  have hCn : Y ≤ Subgroup.normalizer (Cc : Set Γ) := by
    intro g hg
    refine A4.mem_normalizer_inf (Subgroup.le_normalizer hg) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ Subgroup.normalizer (P : Set Γ), ∀ c ∈ Subgroup.centralizer (P : Set Γ),
        g * c * g⁻¹ ∈ Subgroup.centralizer (P : Set Γ) := by
      intro g hg c hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro x hx
      have hx' : g⁻¹ * x * g ∈ P := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
      have h := hc _ hx'
      calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
        _ = g * c * g⁻¹ * x := by group
    refine ⟨fun hc => key g (hPn hg) c hc, fun hc => ?_⟩
    have := key g⁻¹ (inv_mem (hPn hg)) _ hc
    simpa [mul_assoc] using this
  set Z₀ : Subgroup Cc := P.subgroupOf Cc with hZ₀
  have hZc : Z₀ ≤ Subgroup.center Cc := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2.2 z (Subgroup.mem_subgroupOf.mp hz)).symm
  have : Z₀.Normal := Subgroup.normal_of_le_center hZc
  have hquot : IsPGroup 2 (Cc ⧸ Z₀) := by
    intro r
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨k, hk⟩ := hY2 c c.2.1
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hk
  have hnil : Group.IsNilpotent Cc := by
    have := hquot.isNilpotent
    exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z₀)
      (by rw [QuotientGroup.ker_mk']; exact hZc)
  have hAC : A ≤ Cc := le_inf hAY hAP
  have hA2' : IsPGroup 2 (A.subgroupOf Cc) := hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  obtain ⟨S, hS⟩ := hA2'.exists_le_sylow
  have hSn := Group.IsNilpotent.sylow_normal hnil 2 S
  have hSO : (S : Subgroup Cc) ≤ CFSG.Open.pCore 2 Cc := le_pCore 2 hSn S.isPGroup'
  have hCO : pCoreOf 2 Cc ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Cc).trans inf_le_left)
      (hCn.trans (normalizer_le_normalizer_pCoreOf 2 Cc)) (pCoreOf_isPGroup 2 Cc)
  rw [eq_bot_iff]
  intro a ha
  have h1 : a ∈ pCoreOf 2 Cc := ⟨⟨a, hAC ha⟩, hSO (hS (Subgroup.mem_subgroupOf.mpr ha)), rfl⟩
  rw [← hO2]
  exact hCO h1

end Sections

section Main

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

omit [Finite G] in
private theorem le_centralizer_omegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp
    (((Subgroup.closure_le _).mpr fun _ hz => hz.1 :
      quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G)).trans inf_le_right)

theorem commutator_ne_bot_of_isUniqueM (hyp : MultipleCentralizerHypothesis G T)
    {X M : Subgroup G} (hM : IsUniqueM (X ⊔ T) M) : ⁅quasithinOmegaOneCenter T, X⁆ ≠ ⊥ := by
  intro h
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hC₁, hC₂⟩ := hyp.two_centralizer_maximal
  have hXC : X ⊔ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    refine sup_le ?_ (le_centralizer_omegaOneCenter T)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h
  exact hne ((hM.2 M₁ ⟨hM₁, hXC.trans hC₁⟩).trans (hM.2 M₂ ⟨hM₂, hXC.trans hC₂⟩).symm)

theorem eq_five_of_isUniqueM (hyp : MultipleCentralizerHypothesis G T) (h4 : Stmt1542Four G T)
    {X : Subgroup G} {p : ℕ} (hX : IsSmallXi T X) (hXp : (pCoreOf 2 X).relIndex X = p)
    (hp3 : 3 < p) {M : Subgroup G} (hM : IsUniqueM (X ⊔ T) M)
    (hZX : ⁅quasithinOmegaOneCenter T, X⁆ ≠ ⊥) : p = 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p', hp', hp'2, hidx⟩ := hX.2.2.2
  obtain rfl : p' = p := hidx.symm.trans hXp
  have : Fact p'.Prime := ⟨hp'⟩
  set T' : Sylow 2 G := hyp.sylow.1.toSylow hyp.sylow.2 with hT'
  have hT'c : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  set Z := quasithinOmegaOneCenter T with hZdef
  have hXN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hXTc : CharTwo (X ⊔ T) := charTwo_of_inH hyp.qtke.2.1 T' (hT'c ▸ hX.2.2.1)
  have hTXT : (T' : Subgroup G) ≤ X ⊔ T := hT'c ▸ le_sup_right
  have hZ : Z ≤ quasithinOmegaOneCenter (T' : Subgroup G) := by rw [hT'c]
  set V := conjClosure Z (X ⊔ T) with hVdef
  have hV : IsTwoReducedIn (X ⊔ T) V := isTwoReducedIn_conjClosure (X ⊔ T) T' hTXT hXTc hZ
  have hVc : V ≤ centerOf (pCoreOf 2 (X ⊔ T)) :=
    (conjClosure_le_centerOf_pCoreOf (X ⊔ T) T' hTXT hXTc hZ).1
  have hZV : Z ≤ V := le_conjClosure Z (X ⊔ T)
  have hVne : V ≠ ⊥ := by
    have := hyp.simple
    have hTne : T ≠ ⊥ := hT'c ▸ sylow_ne_bot hyp.nonabelian T'
    exact fun h => quasithinOmegaOneCenter_ne_bot hyp.sylow.1 hTne (le_bot_iff.mp (h ▸ hZV))
  have hTM : (T' : Subgroup G) ≤ M := hT'c ▸ le_sup_right.trans hM.1.2
  have hMc : CharTwo M := hyp.qtke.2.1 M hM.1.1.1 ⟨T', hTM⟩
  have hVM : V ≤ pCoreOf 2 M :=
    (conjClosure_mono le_rfl hM.1.2).trans
      ((conjClosure_le_centerOf_pCoreOf M T' hTM hMc hZ).1.trans inf_le_left)
  have hO2V : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := by
    have h1 : pCoreOf 2 X ≤ pCoreOf 2 (X ⊔ T) := A4.pCoreOf_le_of_subnormal 2
      (A4.subnormal_of_normal le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer hXN))
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((hVc hv).2 y (h1 hy)).symm
  have hXV : X ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 X := by
    set A := X ⊓ Subgroup.centralizer (V : Set G)
    have hOA : pCoreOf 2 X ≤ A := le_inf (pCoreOf_le 2 X) hO2V
    have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) A X hOA inf_le_left
    rw [hXp] at hmul
    rcases (Nat.dvd_prime hp').mp (Dvd.intro _ hmul) with h | h
    · exact Subgroup.relIndex_eq_one.mp h
    · exfalso
      rw [h] at hmul
      have h1 : A.relIndex X = 1 := by
        have := hp'.pos
        nlinarith
      have hXA : X ≤ A := Subgroup.relIndex_eq_one.mp h1
      apply hZX
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact (hXA.trans inf_le_right).trans (Subgroup.centralizer_le hZV)
  set D := (X ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hD
  have hD2 : IsPGroup 2 D := by
    rintro ⟨d, hdXT, hdV⟩
    have hd' : d ∈ (↑(X ⊔ T) : Set G) := hdXT
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hX.2.1] at hd'
    obtain ⟨x, hx, t, ht, rfl⟩ := hd'
    obtain ⟨k, hk⟩ := hyp.sylow.1 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨x', hx', he⟩ := A4.exists_pow_mul_eq hx (hX.2.1 ht) (2 ^ k)
    rw [hk', mul_one] at he
    have hx'V : x' ∈ Subgroup.centralizer (V : Set G) := he ▸ Subgroup.pow_mem _ hdV _
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 X ⟨x', hXV ⟨hx', hx'V⟩⟩
    have hm' : x' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨k + m, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, he, hm']
  have hDn : X ⊔ T ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    refine A4.mem_normalizer_inf (Subgroup.le_normalizer hg) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ Subgroup.normalizer (V : Set G),
        ∀ c ∈ Subgroup.centralizer (V : Set G), g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      intro g hg c hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro x hx
      have hx' : g⁻¹ * x * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
      have h := hc _ hx'
      calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
        _ = g * c * g⁻¹ * x := by group
    refine ⟨fun hc => key g (hV.2.1 hg) c hc, fun hc => ?_⟩
    have := key g⁻¹ (inv_mem (hV.2.1 hg)) _ hc
    simpa [mul_assoc] using this
  have hDT : D ≤ T := (le_pCoreOf_of_le_normalizer 2 inf_le_left hDn hD2).trans
    (hT'c ▸ pCoreOf_two_le_sylow (X ⊔ T) T' hTXT)
  have hcent : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 D := by
    rw [le_antisymm (pCoreOf_le 2 D) (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
      hD2)]
    exact le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf hDT inf_le_right)
  have hq := h4 (X ⊔ T) M V hX.2.2.1 hM hVne hV hcent hVM
  let _ := commGroupOfElemAbelian hV.2.2.1
  set Xb := autOn (X ⊔ T) V with hXb
  have hq' : qhatOf Xb ≤ 2 := hq
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf Xb = r := by
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hq')
    exact ⟨r, hr.symm⟩
  have hr2 : r ≤ 2 := by
    rw [hr] at hq'
    exact WithTop.coe_le_coe.mp (by simpa using hq')
  obtain ⟨⟨A, hA, hAk, hAr⟩, -⟩ := kq_eq_coe_iff.mp hr
  have hAS : A ∈ kRle Xb 3 r := ⟨⟨hA, hAr.le⟩, hAk⟩
  obtain ⟨A₀, -, hA₀⟩ := (Set.toFinite (kRle Xb 3 r)).exists_le_minimal hAS
  have hA₀Q : A₀ ∈ QhatStar Xb :=
    ⟨r, hr, hr2, hA₀.1, fun B hB hBA => le_antisymm hBA (hA₀.2 hB hBA)⟩
  have hVsq : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2.2.1.2 v v.2)
  set N := Subgroup.normalizer (V : Set G) with hN
  have hXVN : X ≤ N := le_sup_left.trans hV.2.1
  have hTVN : T ≤ N := le_sup_right.trans hV.2.1
  set X₁ := autOn X V with hX₁
  have hX₁b : X₁ ≤ Xb := A4.autOn_mono le_sup_left
  have hconj : ∀ g : N, ∀ h : N, conjAct V g * conjAct V h * (conjAct V g)⁻¹ =
      conjAct V (g * h * g⁻¹) := fun g h => by simp
  have hX₁p : IsPGroup p' X₁ := by
    rintro ⟨_, x, hx, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hxp := pow_mem_pCoreOf_of_relIndex hXp (Subgroup.mem_subgroupOf.mp hx)
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    exact A4.conjAct_eq_one_iff.mpr (hO2V hxp)
  have hXbN : Xb ≤ Subgroup.normalizer (X₁ : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * x * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXN (Subgroup.mem_subgroupOf.mp hg)) x).mp
      (Subgroup.mem_subgroupOf.mp hx)
  have hX₁P : X₁ ≤ pCoreOf p' Xb := le_pCoreOf_of_le_normalizer p' hX₁b hXbN hX₁p
  have hXb2 : ∀ b ∈ Xb, ∃ k : ℕ, b ^ 2 ^ k ∈ X₁ := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ (↑(X ⊔ T) : Set G) := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hX.2.1] at hg'
    obtain ⟨x, hx, t, ht, he⟩ := hg'
    have hgxt : g = ⟨x, hXVN hx⟩ * ⟨t, hTVN ht⟩ := Subtype.ext he.symm
    obtain ⟨k, hk⟩ := hyp.sylow.1 ⟨t, ht⟩
    have hk' : (⟨t, hTVN ht⟩ : N) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have htX : conjAct V ⟨t, hTVN ht⟩ ∈ Subgroup.normalizer (X₁ : Set (MulAut V)) :=
      hXbN ⟨⟨t, hTVN ht⟩, Subgroup.mem_subgroupOf.mpr (le_sup_right (a := X) ht), rfl⟩
    obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq
      (⟨⟨x, hXVN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩ : conjAct V ⟨x, hXVN hx⟩ ∈ X₁)
      htX (2 ^ k)
    refine ⟨k, ?_⟩
    rw [hgxt, map_mul, hxe, ← map_pow, hk', map_one, mul_one]
    exact hx'
  have hO2b : pCoreOf 2 Xb = ⊥ := by
    rw [pCoreOf, pCore_autOn_eq_bot hV, Subgroup.map_bot]
  have hD : ⁅pCoreOf p' Xb, A₀⁆ ≠ ⊥ := by
    intro hbot
    have hA₀C : A₀ ≤ Subgroup.centralizer (X₁ : Set (MulAut V)) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
      exact Subgroup.le_centralizer_iff.mp (hX₁P.trans hbot)
    exact hA₀.1.1.1.2.1 (eq_bot_of_le_centralizer_of_pow hO2b hXbN hXb2 hA₀.1.1.1.1
      hA₀.1.1.1.2.2.isPGroup hA₀C)
  obtain ⟨h35, -⟩ := D2_13 hVsq hr hA₀Q hp'2 rfl hD
  omega

theorem isSmallXiF_of_commutator_ne_bot (hyp : MultipleCentralizerHypothesis G T)
    {X : Subgroup G} (hX : IsSmallXi T X) (hZX : ⁅quasithinOmegaOneCenter T, X⁆ ≠ ⊥) :
    IsSmallXiF T X := by
  set T' : Sylow 2 G := hyp.sylow.1.toSylow hyp.sylow.2 with hT'
  have hT'c : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hXN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hXTc : CharTwo (X ⊔ T) := charTwo_of_inH hyp.qtke.2.1 T' (hT'c ▸ hX.2.2.1)
  have hTXT : (T' : Subgroup G) ≤ X ⊔ T := hT'c ▸ le_sup_right
  have hXne : X ≠ ⊥ := by
    intro h
    obtain ⟨p, hp, -, hidx⟩ := hX.2.2.2
    rw [Subgroup.relIndex_eq_one.mpr (h ▸ bot_le : X ≤ pCoreOf 2 X)] at hidx
    exact hp.one_lt.ne hidx
  have hXc : IsXClass X := ⟨hXne, hX.1, A4.charTwo_of_normal le_sup_left hXN hXTc⟩
  refine ⟨hX, hXc, ?_⟩
  have hsub : IsSubnormal X (X ⊔ T) :=
    A4.subnormal_of_normal le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer hXN)
  refine (a4_9 hXc hsub).mp fun h => hZX (le_bot_iff.mp (h ▸ Subgroup.commutator_mono ?_ le_rfl))
  have hZc := omegaOneCenter_le_centerOf_pCoreOf (X ⊔ T) T' hTXT hXTc
  rw [hT'c] at hZc
  refine (Subgroup.closure_le _).mpr fun z hz => Subgroup.subset_closure ⟨?_, hz.2⟩
  exact hZc (Subgroup.subset_closure hz)

end Main

theorem stmt1543_of (hC226 : InputC226) {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) (h3 : Stmt1542Three G T)
    (h4 : Stmt1542Four G T) : Stmt1543 G T := by
  intro X p hX hXp hmax hp3
  obtain ⟨M, hM⟩ := exists_isUniqueM_of_isSmallXi hC226 hyp h2 h3 hX hXp hmax hp3
  have hZX := commutator_ne_bot_of_isUniqueM hyp hM
  obtain ⟨p', hp', hp'2, hidx⟩ := hX.2.2.2
  obtain rfl : p' = p := hidx.symm.trans hXp
  have : Fact p'.Prime := ⟨hp'⟩
  refine ⟨⟨hX, M, hM⟩, fun M' hM' => ?_, hZX, isSmallXiF_of_commutator_ne_bot hyp hX hZX,
    eq_five_of_isUniqueM hyp h4 hX hXp hp3 hM hZX⟩
  have h1 := le_O2pOf_of_isSmallXi hyp h2 h3 hX hXp hmax hp3 hM'
  exact ⟨h1, pCoreOf_le_of_le_O2pOf hp'2 h1⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
