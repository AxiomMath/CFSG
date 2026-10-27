module

public import CFSG.Quasithin.H13.L32A767l
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.H13.L32A767g
public import CFSG.Quasithin.H13.L32A767h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (A : Set G) → h ∈ Subgroup.normalizer (B : Set G) →
      A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj h).toMonoidHom := by
    intro h hhA hhB
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hhA a).mp ha)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hhB b).mp hb)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key g hA hB hx
  · intro hx
    have := key g⁻¹ (inv_mem hA) (inv_mem hB) hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem T_le_normalizer_R1 : T ≤ Subgroup.normalizer
    (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
  le_sup_right.trans (le_normalizer_pCoreOf 2 _)

theorem T_le_normalizer_dKR1 (h : Hyp147 G T L V) (h63 : Thm14_7_63) :
    T ≤ Subgroup.normalizer
      ((dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Subgroup G) : Set G) := fun _ ht =>
  mem_normalizer_sup_of_mem
    (mK_le_normalizer_dK (le_normalizer_oTwoUpper _ (T_le_hz h h63 ht))) (T_le_normalizer_R1 ht)

theorem charTwo_dKR1 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    CharTwo (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) := by
  have hTH := T_le_hz h h63
  have hHK : hz T V ≤ mK T V := le_normalizer_oTwoUpper _
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hDT : dK T V ⊔ T ≤ mK T V := sup_le (fun d hd => hd.1) (hTH.trans hHK)
  have hO : pCoreOf 2 (kz T V) ≤ pCoreOf 2 (dK T V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_kz_le_dK.trans le_sup_left)
      (hDT.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hC : CharTwo (dK T V ⊔ T) := charTwo_of_inH h.fsu.qtke.2.1 S
    ⟨by rw [hS]; exact le_sup_right, fun h0 =>
      pCoreOf_kz_ne_bot h hMod h63 (le_bot_iff.mp (h0 ▸ hO))⟩
  refine A4.charTwo_of_normal (sup_le_sup_left hRT _) (sup_le ?_ ?_) hC
  · exact fun d hd => Subgroup.le_normalizer (Subgroup.mem_sup_left hd)
  · exact T_le_normalizer_dKR1 h h63

theorem inf_hz_le_R1 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⊓ hz T V ≤
      pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  have hTH := T_le_hz h h63
  have hRT : R ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hRD : R ≤ Subgroup.normalizer (dK T V : Set G) :=
    (hRT.trans (hTH.trans (le_normalizer_oTwoUpper _))).trans mK_le_normalizer_dK
  intro x hx
  obtain ⟨hxX, hxH⟩ := Subgroup.mem_inf.mp hx
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRD] at hxX
  obtain ⟨r, hr, d, hd, rfl⟩ := hxX
  have hrH : r ∈ hz T V := hTH (hRT hr)
  have hdH : d ∈ hz T V := by
    rw [show d = r⁻¹ * (r * d) by group]
    exact mul_mem (inv_mem hrH) hxH
  exact mul_mem hr (pCoreOf_hz_le_R1_of h hMod h63 (inf_dK_le h hMod h63 ⟨hdH, hd⟩))

theorem fsuV1_le_omegaOneCenter_R1 (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) :
    fsuV1 T V ≤ quasithinOmegaOneCenter (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hTH := T_le_hz h h63
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hV1c : ∀ a ∈ fsuV1 T V, ∀ b ∈ fsuV1 T V, a * b = b * a := by
    intro a ha b hb
    have := normalizer_eq_centralizer_of_card_two hV1
    have hbN : b ∈ Subgroup.normalizer (fsuV1 T V : Set G) := Subgroup.le_normalizer hb
    rw [this] at hbN
    exact Subgroup.mem_centralizer_iff.mp hbN a ha
  have hV1H : fsuV1 T V ≤ hz T V := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hV1c b hb a ha
  have hV1Q : fsuV1 T V ≤ pCoreOf 2 (hz T V) := by
    refine le_pCoreOf_of_le_normalizer 2 hV1H (Subgroup.centralizer_le_normalizer _) ?_
    refine IsPGroup.of_card (n := 1) ?_
    rw [hV1, pow_one]
  intro v hv
  refine Subgroup.subset_closure ⟨⟨pCoreOf_hz_le_R1_of h hMod h63 (hV1Q hv), ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (Subgroup.mem_centralizer_iff.mp (hTH (hRT hr)) v hv).symm
  · have : Nat.card ↥(Subgroup.zpowers v) ∣ 2 := hV1 ▸ Subgroup.card_dvd_of_le
      (Subgroup.zpowers_le.mpr hv)
    rw [Nat.card_zpowers] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this

theorem R1_inf_centralizer_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)))
        (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Set G) =
      pCoreOf 2 (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) := by
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set X := dK T V ⊔ R with hX
  set E' := conjClosure (quasithinOmegaOneCenter R) X with hE'
  have hS := isSylowTwoOf_R1_dK h hMod h63
  have hC := charTwo_dKR1 h hMod h63
  obtain ⟨hE'O, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hS hC (le_refl _)
  have hOR : pCoreOf 2 X ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hOC : pCoreOf 2 X ≤ Subgroup.centralizer (E' : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hE'O he)).2 o ho).symm
  have hV1E : fsuV1 T V ≤ E' :=
    (fsuV1_le_omegaOneCenter_R1 h hMod h63).trans (le_conjClosure _ _)
  have hXE : X ≤ Subgroup.normalizer (E' : Set G) := le_normalizer_conjClosure _ _
  have hCX : X ⊓ Subgroup.centralizer (E' : Set G) ≤ pCoreOf 2 X := by
    have hCH : X ⊓ Subgroup.centralizer (E' : Set G) ≤ R := fun x hx =>
      inf_hz_le_R1 h hMod h63 ⟨hx.1, Subgroup.centralizer_le hV1E hx.2⟩
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => ?_)
      ((pCoreOf_isPGroup 2 _).to_le hCH)
    refine mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) ?_
    refine mem_normalizer_of_forall_conj_mem fun c hc => ?_
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro e he
    have he' : x⁻¹ * e * x ∈ E' := by
      have := (Subgroup.mem_normalizer_iff.mp (hXE (inv_mem hx)) e).mp he
      simpa using this
    have := hc _ he'
    calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [this]
      _ = x * c * x⁻¹ * e := by group
  refine le_antisymm (fun r hr => hCX ⟨hS.1 hr.1, hr.2⟩) (le_inf hOR hOC)

theorem not_thompsonJ_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (hC137 : U3.C137Statement)
    (hN : ¬ mK T V ≤ hz T V) :
    ¬ thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)))
        (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Set G) := by
  intro hJ
  have h13322 := stmt13_3_2_two_of h1332
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set X := dK T V ⊔ R with hX
  set E' := conjClosure (quasithinOmegaOneCenter R) X with hE'
  have hS := isSylowTwoOf_R1_dK h hMod h63
  have hC := charTwo_dKR1 h hMod h63
  obtain ⟨hE'O, hE'e, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hS hC (le_refl _)
  have hOR : pCoreOf 2 X ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hb : baum R = baum (pCoreOf 2 X) := by
    rw [← R1_inf_centralizer_eq h hMod h63]
    exact baum_eq_baum_centralizer hE'e ((hE'O.trans inf_le_left).trans hOR)
      (le_inf (iSup₂_le fun _ hA => hA.1) hJ)
  have hXb : X ≤ Subgroup.normalizer (baum R : Set G) := by
    rw [hb]
    exact (le_normalizer_pCoreOf 2 X).trans
      (normalizer_le_normalizer_of_characteristic (inf_le_left) (C1GN.characteristic_baum _))
  have hXM := hXb.trans (normalizer_baum_R1_le h hMod h63 h1222 h1332 h1334 hF hC137)
  obtain ⟨d, hd, hd1, hodd⟩ := exists_odd_mem_dK h hMod h63 hN
  have hdT := inf_dK_le_T h hMod h63 h13322 ⟨hd, hXM (Subgroup.mem_sup_left hd)⟩
  obtain ⟨n, hn⟩ := h.fsu.sylow.1 ⟨d, hdT⟩
  have hd2 : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime (orderOf d) (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact hd1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hd2)))

end CFSG.Quasithin.H13.L32A
