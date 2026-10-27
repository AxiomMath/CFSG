module

public import CFSG.Quasithin.H13.NQS13410O

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem le_normalizer_centralizer_of {X N : Subgroup G} (h : N ≤ normalizer (X : Set G)) :
    N ≤ normalizer (centralizer (X : Set G) : Set G) :=
  A5.le_normalizer_of_forall_conj_mem fun g hg c hc => mem_centralizer_iff.2 fun x hx => by
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ X := (mem_normalizer_iff.mp (inv_mem (h hg)) x).mp hx
    have h1 := mem_centralizer_iff.mp hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group

theorem not_two_copies_of_a6 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {K U I : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ K) (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥U] (hnatU : BinaryNaturalSL (V := ↥U) (autOn K U) ⊤ ⊥ 3 1)
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (ho2Z : A6.o2Z K = K ⊓ centralizer (U : Set G)) (hUI : U ⊓ I = ⊥)
    (hWe : IsElemAbelian 2 (U ⊔ I)) (hKI : K ≤ normalizer (I : Set G)) (φ : ↥U ≃* ↥I)
    (hφ : ∀ k ∈ K, ∀ (u : ↥U) (hu : k * (u : G) * k⁻¹ ∈ U),
      ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹)
    (hTW : T ≤ normalizer ((U ⊔ I : Subgroup G) : Set G))
    (hWR : U ⊔ I ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hZ : quasithinOmegaOneCenter T ≤ U ⊔ U3.cZ T K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := U ⊔ I with hWdef
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hRdef
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hWe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hIU : I ≤ normalizer (U : Set G) :=
    A5.le_normalizer_of_forall_conj_mem fun i hi u hu => by
      rw [hcomm i (mem_sup_right hi) u (mem_sup_left hu), mul_inv_cancel_right]
      exact hu
  have hKW : K ≤ normalizer (W : Set G) := le_normalizer_sup_of hIU hKU hKI
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hUW : U ≤ W := le_sup_left
  have hUR : U ≤ R := hUW.trans hWR
  have hUT : U ≤ T := hUR.trans hRT
  obtain ⟨C⟩ := exists_l3Coords hnatU
  have htop := autOn_eq_top_of_l32 hnatU
  have hU8 : Nat.card ↥U = 8 := card_eq_eight_of_l32 hnatU
  have hI8 : Nat.card ↥I = 8 := by rw [← Nat.card_congr φ.toEquiv, hU8]
  have hW64 : Nat.card ↥W = 64 := by
    rw [hWdef, card_sup_eq_mul hUI hIU, hU8, hI8]
  have hCU2 : IsPGroup 2 ↥(K ⊓ centralizer (U : Set G)) := by
    rw [← ho2Z]
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)
  have hCW2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) :=
    hCU2.to_le (inf_le_inf_left K (centralizer_le hUW))
  set Q := (K ⊔ T) ⊓ centralizer (W : Set G) with hQdef
  have hKTW : K ⊔ T ≤ normalizer (W : Set G) := sup_le hKW hTW
  have hQ2 : IsPGroup 2 ↥Q := isPGroup_sup_inf_centralizer hTsyl.2.1 hTK hCW2
  have hQn : K ⊔ T ≤ normalizer (Q : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun g hg c hc => ?_
    obtain ⟨hcKT, hcW⟩ := mem_inf.1 hc
    refine mem_inf.2 ⟨mul_mem (mul_mem hg hcKT) (inv_mem hg), mem_centralizer_iff.2 fun x hx => ?_⟩
    have hgW : g ∈ normalizer (W : Set G) := hKTW hg
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ W := (mem_normalizer_iff.mp (inv_mem hgW) x).mp hx
    have h1 := mem_centralizer_iff.mp hcW _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  have hQO : Q ≤ pCoreOf 2 (K ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hQn hQ2
  have hQT : Q ≤ T := hQO.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
  have hQR : Q ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (sup_le (hL1K.trans (le_sup_left.trans hQn)) (le_sup_right.trans hQn)) hQ2
  have hQW : Q ≤ centralizer (W : Set G) := inf_le_right
  have hU1 : U ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hU8; omega
  obtain ⟨x₀', hx₀U, hx₀T, hx₀1'⟩ := exists_mem_centralizer_ne_one hKf.1.1 hUT hTU hU1
  set x₀ : ↥U := ⟨x₀', hx₀U⟩ with hx₀def
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (congrArg Subtype.val h)
  obtain ⟨y, hyK, ⟨m, hm, hym⟩, hyU, hy3U, hyfix⟩ := exists_three_of_l32 hKU hnatU hsyl
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨s, hs⟩ := hCU2 ⟨_, mem_inf.2 ⟨pow_mem hyK 3, hy3U⟩⟩
    have hs' : (y ^ 3) ^ 2 ^ s = 1 := by
      have h2 := congrArg Subtype.val hs
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hy1 : y ≠ 1 := fun h => hyU (h ▸ one_mem _)
  have hyZ := mem_centralizer_Z_of hTU hZ hyK hyfix
  have hyL1 : y ∈ L₁ := mem_L1_of_pow_three h1332 h1228 S he hyZ (k := 1) (by simpa using hy3)
  have hyR : y ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hyL1)
  set yN : ↥(normalizer (U : Set G)) := ⟨y, hKU hyK⟩ with hyN
  have hρy3 : C.ρ yN ^ 3 = 1 := by
    rw [← map_pow]
    have : yN ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hyN, Subgroup.coe_one]
      exact hy3)
    rw [this, map_one]
  have hρy1 : C.ρ yN ≠ 1 := fun h => hyU ((C.ker yN).1 h)
  have hρyp : L3.act (C.ρ yN) (C.c x₀) = C.c x₀ := by
    refine (C.fix_iff yN x₀).1 ?_
    show y * x₀' * y⁻¹ = x₀'
    rw [hyfix x₀' hx₀U hx₀T, mul_inv_cancel_right]
  have hRfix : ∀ r ∈ R, r * (x₀ : G) * r⁻¹ = x₀ := fun r hr => by
    show r * x₀' * r⁻¹ = x₀'
    rw [mem_centralizer_iff.mp hx₀T r (hRT hr), mul_inv_cancel_right]
  have hRE : ∀ r : ↥(normalizer (U : Set G)), (r : G) ∈ R → C.ρ r ∈ L3.AS {0, C.c x₀} :=
    fun r hr => C.rho_mem_AS hR2 hx₀1 hRfix yN hρy3 hρy1 hρyp hyR r hr
  have hp0 : C.c x₀ ≠ 0 := C.c_ne_zero hx₀1
  have hRU : R ≤ normalizer (U : Set G) := hRT.trans hTU
  have hRW : R ≤ normalizer (W : Set G) := hRT.trans hTW
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hcontra : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ T → L ⊔ T ≤ normalizer (X : Set G) →
      K ≤ normalizer (X : Set G) → False := by
    intro X hX1 hXT hLX hKX
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨X, hX1, S.h13.sylow.1.to_le hXT, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
    have hM := S.uniqueM.2 M' ⟨hM', hLX.trans hle⟩
    exact hKM (hKX.trans (hM ▸ hle))
  have hRR1 : R = U3.r1Of T L V := (U3.s134Plus_L1 S he).pCoreOf_eq_r1Of
  rcases U3.s134_lemma13_2_2_seven hC137 h1332 S with ⟨Cc, hCB, hC1, hCchar, hCN⟩ | hB
  ·
    have hJ : thompsonJ R ≤ R ⊓ centralizer (W : Set G) := by
      refine iSup₂_le fun A hA => le_inf hA.1 ?_
      by_contra hAC
      have hle := card_le_relIndex_mul_card hWe hWR hA
      have h32 := relIndex_mul_card_le_thirtytwo C hUI hcomm hKU hKI φ hφ htop hU8
        (hA.1.trans hRU) (hA.1.trans hRW) (hA.1.trans hRK) hp0
        (fun a ha => hRE a (hA.1 ha)) hAC
      rw [← hWdef] at h32
      rw [hW64] at hle
      omega
    have hRCW : R ⊓ centralizer (W : Set G) = Q :=
      le_antisymm (fun r hr => mem_inf.2 ⟨mem_sup_right (hRT (mem_inf.1 hr).1), (mem_inf.1 hr).2⟩)
        (le_inf hQR hQW)
    have hBQ : baum R = baum Q := by rw [baum_eq_baum_centralizer hWe hWR hJ, hRCW]
    rw [← hRR1, hBQ] at hCB hCchar
    have := hCchar
    refine hcontra Cc hC1 (hCB.trans (inf_le_left.trans hQT)) hCN ?_
    have h2 : normalizer (baum Q : Set G) ≤ normalizer (Cc : Set G) := by
      have h3 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Cc.subgroupOf (baum Q))
      rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at h3
    exact (le_sup_left.trans hQn).trans ((normalizer_le_normalizer_baum Q).trans h2)
  ·
    have hc16 : (centralizer ({y} : Set G)).relIndex R ≤ 16 :=
      s134_relIndex_R_le_sixteen S hB hyL1 hy3
    set QU := R ⊓ centralizer (U : Set G) with hQUdef
    have hQUR : QU ≤ R := inf_le_left
    have hRQn : R ≤ normalizer (QU : Set G) := fun r hr =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer hr, le_normalizer_centralizer_of hRU hr⟩
    have hyQ : y ∈ normalizer (QU : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨hyR, le_normalizer_centralizer_of hKU hyK⟩
    have hRCy : R ⊓ centralizer ({y} : Set G) ≤ QU := by
      intro r hr
      obtain ⟨hrR, hry⟩ := mem_inf.1 hr
      have hrN : r ∈ normalizer (U : Set G) := hRU hrR
      have hcomm' : C.ρ ⟨r, hrN⟩ * C.ρ yN = C.ρ yN * C.ρ ⟨r, hrN⟩ := by
        have h1 : (⟨r, hrN⟩ * yN : ↥(normalizer (U : Set G))) = yN * ⟨r, hrN⟩ :=
          Subtype.ext (mem_centralizer_singleton_iff.mp hry)
        have h2 := congrArg C.ρ h1
        rwa [map_mul, map_mul] at h2
      have h1 := l3_AS_comm _ hp0 _ hρy3 hρy1 hρyp _ (hRE ⟨r, hrN⟩ hrR) hcomm'
      exact mem_inf.2 ⟨hrR, (C.ker ⟨r, hrN⟩).1 h1⟩
    have hsup' : QU ⊔ (R ⊓ centralizer ({y} : Set G)) = QU := sup_eq_left.2 hRCy
    have hcRQ : (centralizer ({y} : Set G)).relIndex R =
        QU.relIndex R * (centralizer ({y} : Set G)).relIndex QU := by
      have h1 := U3.relIndex_centralizer_eq_mul (x := y) hQUR hRQn
      rwa [hsup'] at h1
    have hRQ : ¬ R ≤ QU := by
      intro hle
      obtain ⟨s, hsTK, hsE, hs1⟩ := C.exists_mem_AS hKU hsyl hx₀1 hx₀T
      have hsT : (s : G) ∈ T := (mem_inf.1 hsTK).1
      set g₁ := (s : G) * y * (s : G)⁻¹ * y⁻¹ with hg₁
      have hg₁L1 : g₁ ∈ L₁ :=
        mul_mem ((mem_normalizer_iff.mp (U3.s134_T_le_normalizer_L1 S hsT) y).mp hyL1)
          (inv_mem hyL1)
      have hg₁N : g₁ ∈ normalizer (U : Set G) :=
        mul_mem (mul_mem (mul_mem s.2 yN.2) (inv_mem s.2)) (inv_mem yN.2)
      have hρg₁ : C.ρ ⟨g₁, hg₁N⟩ = C.ρ s * (C.ρ yN * C.ρ s * (C.ρ yN)⁻¹) := by
        have e : (⟨g₁, hg₁N⟩ : ↥(normalizer (U : Set G))) = s * yN * s⁻¹ * yN⁻¹ := rfl
        have hss : (C.ρ s)⁻¹ = C.ρ s := by
          rw [inv_eq_iff_mul_eq_one]
          exact (L3.AS_elem _ hp0 _ hsE _ hsE).2
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hss]
        group
      obtain ⟨hcE, hc1⟩ := l3_comm_ne _ hp0 _ hρy3 hρy1 hρyp _ hsE hs1
      rw [← hρg₁] at hcE hc1
      obtain ⟨a, m₁, hm₁, hn₁⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₁).ne'
      have hua : (g₁ ^ m₁) ^ 2 ^ a = 1 := by
        rw [← pow_mul, mul_comm m₁, ← hn₁, pow_orderOf_eq_one]
      have huL1 : g₁ ^ m₁ ∈ L₁ := pow_mem hg₁L1 _
      have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
      have huV : g₁ ^ m₁ ∈ normalizer (V : Set G) := S.frame.L_le (hL1L huL1)
      have hρu : S.frame.ρ ⟨g₁ ^ m₁, huV⟩ ∈ A6.K4L := by
        have h16 : S.frame.ρ ⟨g₁ ^ m₁, huV⟩ ^ 16 = 1 := by
          refine U3.pow_sixteen_of_two_pow (k := a) ?_
          rw [← map_pow]
          have h1 : (⟨g₁ ^ m₁, huV⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ a = 1 :=
            Subtype.ext (by simpa using hua)
          rw [h1, map_one]
        exact U3.A4_two_K4 _ (U3.s134_rho_L1 S huV huL1) h16
      have huR : g₁ ^ m₁ ∈ R := s134_pCoreOf_L1_le_R S
        ((U3.s134Plus_L1 S he).mem_pCoreOf_of_K4 (x := ⟨g₁ ^ m₁, huV⟩) huL1 hρu)
      have h1 := (C.ker (⟨g₁, hg₁N⟩ ^ m₁)).2 (mem_inf.1 (hle huR)).2
      rw [map_pow] at h1
      obtain ⟨b, hb⟩ := hm₁
      have hsq : C.ρ ⟨g₁, hg₁N⟩ * C.ρ ⟨g₁, hg₁N⟩ = 1 := (L3.AS_elem _ hp0 _ hcE _ hcE).2
      rw [hb, pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at h1
      exact hc1 h1
    have hRQ4 : 4 ≤ QU.relIndex R := by
      have h1 := U3.relIndex_sup_eq_one_or hy3 hR2 hQUR hRQn hyQ hyR
      rw [hsup'] at h1
      exact h1.resolve_left fun h => hRQ (relIndex_eq_one.mp h)
    have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hWe.2 w w.2)⟩
    have hcW16 := sixteen_le_relIndex_centralizer hUI hcomm hKU hKI φ hφ hW2 hyK hy3 hyU
    have hWQU : W ≤ QU := fun w hw => mem_inf.2 ⟨hWR hw, mem_centralizer_iff.2 fun u hu =>
      hcomm u (hUW hu) w hw⟩
    have hcQ : 16 ≤ (centralizer ({y} : Set G)).relIndex QU :=
      hcW16.trans (U3.relIndex_centralizer_le hWQU)
    have h1 : 4 * 16 ≤ (centralizer ({y} : Set G)).relIndex R := by
      rw [hcRQ]
      exact Nat.mul_le_mul hRQ4 hcQ
    omega

end CFSG.Quasithin.H13.NQS134
