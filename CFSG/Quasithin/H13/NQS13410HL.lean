module

public import CFSG.Quasithin.H13.NQS13410HK
public import CFSG.Quasithin.H13.NQS13410V
public import CFSG.Quasithin.H13.NQS13410X

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

theorem card_W4' : Nat.card ↥W4 = 16 := by
  have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem false_of_hatK_sym (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1W : L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G)) (hhatK : A6.IsHatA6 K)
    (hW : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W) [IsMulCommutative ↥W]
    (hTW : T ≤ normalizer (W : Set G)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (himg : ∀ σ : Perm (Fin 6), (∃ g : ↥(normalizer (W : Set G)), (g : G) ∈ K ∧ ρ g = σ) ↔
      σ ∈ alternatingGroup (Fin 6))
    (hker : ∀ g, ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (hTD : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T → InD6 (ρ g)) {w₀ : G}
    (hw₀Z : w₀ ∈ quasithinOmegaOneCenter T)
    (hfix : ∀ g : ↥(normalizer (W : Set G)), (g : G) * w₀ * (g : G)⁻¹ = w₀ → U3.Pres45 (ρ g))
    (hcount : ∀ A : Subgroup G, A ≤ normalizer (W : Set G) →
      (∀ a : ↥(normalizer (W : Set G)), (a : G) ∈ A → ρ a ∈ U3.K4List) →
      ¬ A ≤ centralizer (W : Set G) →
      (A ⊓ centralizer (W : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G)) <
        Nat.card ↥W)
    {c : G} (hcL1 : c ∈ L₁Of L (fsuV1 T V)) (hc3 : orderOf c = 3)
    (hcW : c ∉ centralizer (W : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hKW : K ≤ normalizer (W : Set G) := hW.2.2.1
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hRT : R ≤ T := s134_R_le_T S
  have hR2 : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hL1TR : L₁ ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hNC : normalizer (W : Set G) ≤ normalizer (centralizer (W : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer W
  have hK0L1 : ∀ d ∈ A6.l0 K, d ^ 3 = 1 → d ≠ 1 → d ∈ L₁ := by
    intro d hd hd3 hd1
    have hdZ : d ∈ A6.o2Z K := oTwoRes_le _ hd
    rw [ho2Z] at hdZ
    obtain ⟨hdK, hdW⟩ := mem_inf.1 hdZ
    have hdZ' := mem_centralizer_Z_of hTW hZW hdK fun w hw _ =>
      (mem_centralizer_iff.mp hdW w hw).symm
    exact mem_L1_of_orderOf_three h1332 h1228 S hdZ' (orderOf_eq_prime hd3 hd1)
  have hcN : c ∈ normalizer (W : Set G) := hL1W hcL1
  set γ := ρ ⟨c, hcN⟩ with hγ
  have hc3' : c ^ 3 = 1 := by rw [← hc3, pow_orderOf_eq_one]
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨c, hcN⟩ : ↥(normalizer (W : Set G))) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hc3')
    rw [this, map_one]
  have hγ1 : γ ≠ 1 := fun h => hcW ((hker _).1 h)
  have hγS : γ ∈ stab45List := (mem_stab45_iff γ).2 ⟨sign_of_cube γ hγ3, hfix _ (by
    rw [← mem_centralizer_iff.mp (hL1Z hcL1) w₀ hw₀Z, mul_inv_cancel_right])⟩
  have hRK4 : ∀ r : ↥(normalizer (W : Set G)), (r : G) ∈ R → ρ r ∈ U3.K4List := by
    intro r hr
    have hsign : Perm.sign (ρ r) = 1 := by
      refine rho_sign_of_comm KGHatA6.hatA6OddInverts_holds hhatK hKW ρ himg hker ho2Z r (hRK hr)
        fun d hd hd3 hdO => ?_
      have hd1 : d ≠ 1 := fun h => hdO (h ▸ one_mem _)
      have hdR : d ∈ normalizer (R : Set G) := hL1TR (mem_sup_left (hK0L1 d hd hd3 hd1))
      have h1 : (r : G) * d * (r : G)⁻¹ * d⁻¹ ∈ R := by
        have h2 : d * (r : G)⁻¹ * d⁻¹ ∈ R := (mem_normalizer_iff.mp hdR _).mp (inv_mem hr)
        have e : (r : G) * d * (r : G)⁻¹ * d⁻¹ = (r : G) * (d * (r : G)⁻¹ * d⁻¹) := by group
        rw [e]
        exact mul_mem hr h2
      obtain ⟨k, hk⟩ := hR2 ⟨_, h1⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hcR : c ∈ normalizer (R : Set G) := hL1TR (mem_sup_left hcL1)
    have hcr : c * r * c⁻¹ ∈ R := (mem_normalizer_iff.mp hcR r).mp hr
    have hD := hTD ((⟨c, hcN⟩ : ↥(normalizer (W : Set G))) * r * ⟨c, hcN⟩⁻¹) (hRT hcr)
    rw [map_mul, map_mul, map_inv] at hD
    exact stab45_conj_D_K4 γ hγS hγ3 hγ1 _ (hTD r (hRT hr)) hsign hD
  have hred := twoReduced_R2 (K ⊔ T)
  have hWe : IsElemAbelian 2 W := ⟨‹_›, fun w hw => hred.2.2.1.2 w (hW.1 hw)⟩
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hWe.2 w w.2)⟩
  have hWK : W ≤ K := by
    rw [← hW.2.2.2.1]
    have hWT : W ≤ T := (hW.1.trans (R2_le_pCoreOf (K ⊔ T))).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
    exact le_normalizer_iff_commutator_le_right.mp (hWT.trans hTK)
  have hWR : W ≤ R := le_R_of_le S hTK hTsyl hL1K hWK hW2 hKW hTW
  have hJ : thompsonJ R ≤ centralizer (W : Set G) := by
    refine iSup₂_le fun A hA => ?_
    by_contra hAC
    have hle := card_le_relIndex_mul_card hWe hWR hA
    have hlt := hcount A (hA.1.trans (hRT.trans hTW)) (fun a ha => hRK4 a (hA.1 ha)) hAC
    omega
  obtain ⟨d, hdL0, hd3, hdO, hdec⟩ := A6.exists_l0_c hhatK.2.1
  have hdL1 : d ∈ L₁ := hK0L1 d hdL0 hd3 (fun h => hdO (h ▸ one_mem _))
  have hdR : d ∈ normalizer (R : Set G) := hL1TR (mem_sup_left hdL1)
  set U := A6.o2Z K with hU
  set I := R ⊓ centralizer (W : Set G) with hI
  have hUK : U ≤ K := A6.o2Z_le_L
  have hOR : pCoreOf 2 K ≤ normalizer (R : Set G) :=
    (pCoreOf_le_T_of_sylow hTK hTsyl).trans (le_sup_right.trans hL1TR)
  have hUR : U ≤ normalizer (R : Set G) := by
    intro x hx
    have hdd : d * d ∈ normalizer (R : Set G) := mul_mem hdR hdR
    rcases hdec x hx with h | h | h
    · exact hOR h
    · have e : x = (d * d)⁻¹ * (d * d * x) := by group
      rw [e]
      exact mul_mem (inv_mem hdd) (hOR h)
    · have e : x = d⁻¹ * (d * x) := by group
      rw [e]
      exact mul_mem (inv_mem hdR) (hOR h)
  have hUI : U ≤ normalizer (I : Set G) :=
    (le_inf hUR ((hUK.trans hKW).trans hNC)).trans inf_normalizer_le_normalizer_inf
  have hIU : I ≤ normalizer (U : Set G) :=
    inf_le_left.trans (hRK.trans A6.normalizer_L_le_o2Z)
  have hTI : T ≤ normalizer (I : Set G) :=
    (le_inf (le_sup_right.trans hL1TR) (hTW.trans hNC)).trans inf_normalizer_le_normalizer_inf
  have hL1I : L₁ ≤ normalizer (I : Set G) :=
    (le_inf (le_sup_left.trans hL1TR) (hL1W.trans hNC)).trans inf_normalizer_le_normalizer_inf
  have hTU : T ≤ normalizer (U : Set G) := hTK.trans A6.normalizer_L_le_o2Z
  have hL1U : L₁ ≤ normalizer (U : Set G) := hL1K.trans A6.normalizer_L_le_o2Z
  have hTUI : T ≤ normalizer ((U ⊔ I : Subgroup G) : Set G) := le_normalizer_sup_of hIU hTU hTI
  have hL1UI : L₁ ≤ normalizer ((U ⊔ I : Subgroup G) : Set G) :=
    le_normalizer_sup_of hIU hL1U hL1I
  have hKUI : K ≤ normalizer ((U ⊔ I : Subgroup G) : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun k hk x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hIU hx
    have hka : k * a * k⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (A6.normalizer_L_le_o2Z (le_normalizer hk)) a).mp ha
    have hkb : k * b * k⁻¹ * b⁻¹ ∈ U := by
      rw [ho2Z]
      obtain ⟨hbR, hbW⟩ := mem_inf.1 hb
      refine mem_inf.2 ⟨?_, ?_⟩
      · have h1 : b * k⁻¹ * b⁻¹ ∈ K := (mem_normalizer_iff.mp (hRK hbR) _).mp (inv_mem hk)
        have e : k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem hk h1
      · exact mul_mem ((mem_normalizer_iff.mp (hNC (hKW hk)) b).mp hbW) (inv_mem hbW)
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left hka) (mem_sup_left hkb)) (mem_sup_right hb)
  set Y := pCoreOf 2 (U ⊔ I) with hY
  have hNY : normalizer ((U ⊔ I : Subgroup G) : Set G) ≤ normalizer (Y : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
  have hY2 : IsPGroup 2 ↥Y := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hIY : I ≤ Y :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right (sup_le hUI le_normalizer)
      (hR2.to_le inf_le_left)
  have hYT : Y ≤ T := by
    have h1 : Y ≤ pCoreOf 2 (Y ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_left
        (sup_le le_normalizer (hTUI.trans hNY)) hY2
    exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right))
  have hYR : Y ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right)
      ((sup_le hL1UI hTUI).trans hNY) hY2
  exact false_of_thompsonJ_le S hhat hKM ((le_inf (B6.thompsonJ_le R) hJ).trans hIY) hYR
    (hKUI.trans hNY)

theorem not_hatK_of_hat (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1W : L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G)) (hhatK : A6.IsHatA6 K)
    (hW : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W) [IsMulCommutative ↥W]
    (hmod : (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
      (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
        FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥))
    (hTW : T ≤ normalizer (W : Set G)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcL0, hcL1, hc3, -, -⟩ := exists_hat_c S hhat
  obtain ⟨-, ⟨hTK, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hcK := mem_K_of_orderOf_three_of_hat h1332 h1228 S hKf hhatK hW (hL1K hcL1) hc3
  by_cases hcW : c ∈ centralizer (W : Set G)
  · have hcZ : c ∈ A6.o2Z K := by
      rw [ho2Z]
      exact mem_inf.2 ⟨hcK, hcW⟩
    have hcK0 : c ∈ A6.l0 K :=
      U3.mem_oTwoRes_of_odd hcZ (Nat.odd_iff.2 rfl : Odd 3) (by rw [← hc3, pow_orderOf_eq_one])
    exact false_of_l0_l0 S hhat hhatK hKM hTK hTsyl hcL0 hcK0 hc3
  have hKW : K ≤ normalizer (W : Set G) := hW.2.2.1
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hred := twoReduced_R2 (K ⊔ T)
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by
    simpa using (hred.2.2.1.2 w (hW.1 w.2)))⟩
  have hNL : normalizer (W : Set G) ≤ normalizer (K : Set G) := by
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨W, hW.2.1, hW2, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
    have := huniqK M' hM' ((sup_le hKW hTW).trans hle)
    exact this ▸ hle
  have hZT : ∀ w ∈ W, w ∈ centralizer (T : Set G) → w ∈ quasithinOmegaOneCenter T := by
    intro w hw hwT
    have hwT' : w ∈ T := ((hW.1.trans (R2_le_pCoreOf (K ⊔ T))).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)) hw
    exact subset_closure ⟨⟨hwT', hwT⟩, hred.2.2.1.2 w (hW.1 hw)⟩
  rcases hmod with h6 | hc5
  · obtain ⟨R⟩ := exists_rawData4 hKW h6.1
    obtain ⟨F⟩ := exists_frame4 R hNL hKf.1.1 hTW hsyl
    have hfixiff : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
        (g : G) * w * (g : G)⁻¹ = w ↔ act4f (F.ρ g) (F.ψ w) = F.ψ w := by
      intro g w
      have h1 := F.equiv g w
      constructor
      · intro h
        have h2 : conjAct W g w = w := Subtype.ext (by rw [A5.conjAct_val]; exact h)
        rw [h2] at h1
        exact (congrArg Subtype.val h1).symm
      · intro h
        have h2 : F.ψ (conjAct W g w) = F.ψ w := by
          rw [h1]
          exact Subtype.ext h
        have h3 := congrArg Subtype.val (F.ψ.injective h2)
        rw [A5.conjAct_val] at h3
        exact h3
    have hker : ∀ g, F.ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G) := by
      intro g
      constructor
      · intro h1
        refine mem_centralizer_iff.2 fun w hw => ?_
        have h2 := (hfixiff g ⟨w, hw⟩).2 (by rw [h1]; exact act4f_one _ (F.ψ ⟨w, hw⟩).2)
        calc w * g = g * w * (g : G)⁻¹ * g := by rw [h2]
          _ = g * w := by group
      · intro h1
        refine act4f_faithful _ fun x hx => ?_
        set w : ↥W := F.ψ.symm ⟨x, hx⟩ with hw
        have hψw : (F.ψ w : P6) = x := by rw [hw, MulEquiv.apply_symm_apply]
        have h2 := (hfixiff g w).1 (by rw [← mem_centralizer_iff.mp h1 w w.2, mul_inv_cancel_right])
        rw [hψw] at h2
        exact h2
    set w₀ : ↥W := F.ψ.symm ⟨e0123, inW4_e0123⟩ with hw₀
    have hψw₀ : (F.ψ w₀ : P6) = e0123 := by rw [hw₀, MulEquiv.apply_symm_apply]
    have hw₀T : (w₀ : G) ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      have hD := F.T_D ⟨t, F.T_le ht⟩ ht
      have h1 := (hfixiff ⟨t, F.T_le ht⟩ w₀).2 (by rw [hψw₀]; exact act4f_e0123_of_inD6 _ hD)
      calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
        _ = w₀ * t := by rw [h1]
    have hfix : ∀ g : ↥(normalizer (W : Set G)), (g : G) * w₀ * (g : G)⁻¹ = w₀ →
        U3.Pres45 (F.ρ g) := fun g hg => by
      have h1 := (hfixiff g w₀).1 hg
      rw [hψw₀] at h1
      exact pres45_of_act4f_fix _ h1
    have hcount : ∀ A : Subgroup G, A ≤ normalizer (W : Set G) →
        (∀ a : ↥(normalizer (W : Set G)), (a : G) ∈ A → F.ρ a ∈ U3.K4List) →
        ¬ A ≤ centralizer (W : Set G) →
        (A ⊓ centralizer (W : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G)) <
          Nat.card ↥W := by
      intro A hAN hAK hA
      have h16 : Nat.card ↥W = 16 := by rw [Nat.card_congr F.ψ.toEquiv, card_W4']
      rw [h16]
      exact relIndex_mul_card_lt_of_count F.ρ hker act4f InW4 (fun w => (F.ψ w : P6))
        (fun a b h => F.ψ.injective (Subtype.ext h)) (fun w => (F.ψ w).2) hfixiff
        k4_card_mul_lt_W4 hAN hAK hA
    exact false_of_hatK_sym h1332 h1228 S hhat hKf hKM hL1K hL1Z hL1W hhatK hW hTW hZW ho2Z
      F.ρ F.image_L hker F.T_D (hZT w₀ w₀.2 hw₀T) hfix hcount hcL1 hc3 hcW
  · obtain ⟨R⟩ := exists_rawData6 hKW hc5.2.2
    obtain ⟨F⟩ := exists_frame5 R hNL hKf.1.1 hTW hsyl
    have hfixiff : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
        (g : G) * w * (g : G)⁻¹ = w ↔ G6.permAct 6 (F.ρ g) (F.ψ w) = F.ψ w := by
      intro g w
      have h1 := F.equiv g w
      constructor
      · intro h
        have h2 : conjAct W g w = w := Subtype.ext (by rw [A5.conjAct_val]; exact h)
        rw [h2] at h1
        exact (congrArg Subtype.val h1).symm
      · intro h
        have h2 : F.ψ (conjAct W g w) = F.ψ w := by
          rw [h1]
          exact Subtype.ext h
        have h3 := congrArg Subtype.val (F.ψ.injective h2)
        rw [A5.conjAct_val] at h3
        exact h3
    have hker : ∀ g, F.ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G) := by
      intro g
      constructor
      · intro h1
        refine mem_centralizer_iff.2 fun w hw => ?_
        have h2 := (hfixiff g ⟨w, hw⟩).2 (by rw [h1, map_one]; rfl)
        calc w * g = g * w * (g : G)⁻¹ * g := by rw [h2]
          _ = g * w := by group
      · intro h1
        refine permAct_core_faithful _ fun x hx => ?_
        set w : ↥W := F.ψ.symm ⟨x, G6.mem_coreMod.2 hx⟩ with hw
        have hψw : ((F.ψ w : ↥(G6.coreMod 6)) : G6.PermMod 6) = x := by
          rw [hw, MulEquiv.apply_symm_apply]
        have h2 := (hfixiff g w).1 (by rw [← mem_centralizer_iff.mp h1 w w.2, mul_inv_cancel_right])
        rw [hψw] at h2
        exact h2
    set w₀ : ↥W := F.ψ.symm ⟨e45, mem_coreMod_e45⟩ with hw₀
    have hψw₀ : ((F.ψ w₀ : ↥(G6.coreMod 6)) : G6.PermMod 6) = e45 := by
      rw [hw₀, MulEquiv.apply_symm_apply]
    have hw₀T : (w₀ : G) ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      have hD := F.T_D ⟨t, F.T_le ht⟩ ht
      have h1 := (hfixiff ⟨t, F.T_le ht⟩ w₀).2 (by rw [hψw₀]; exact permAct_e45_of_inD6 _ hD)
      calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
        _ = w₀ * t := by rw [h1]
    have hfix : ∀ g : ↥(normalizer (W : Set G)), (g : G) * w₀ * (g : G)⁻¹ = w₀ →
        U3.Pres45 (F.ρ g) := fun g hg => by
      have h1 := (hfixiff g w₀).1 hg
      rw [hψw₀] at h1
      exact pres45_of_permAct_fix _ h1
    have hcount : ∀ A : Subgroup G, A ≤ normalizer (W : Set G) →
        (∀ a : ↥(normalizer (W : Set G)), (a : G) ∈ A → F.ρ a ∈ U3.K4List) →
        ¬ A ≤ centralizer (W : Set G) →
        (A ⊓ centralizer (W : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G)) <
          Nat.card ↥W := by
      intro A hAN hAK hA
      rw [hc5.1]
      exact relIndex_mul_card_lt_of_count F.ρ hker (fun σ x => G6.permAct 6 σ x)
        (fun x : P6 => ∑ i, Multiplicative.toAdd x i = 0)
        (fun w => ((F.ψ w : ↥(G6.coreMod 6)) : G6.PermMod 6))
        (fun a b h => F.ψ.injective (Subtype.ext h)) (fun w => G6.mem_coreMod.1 (F.ψ w).2)
        hfixiff U3.k4_card_mul_lt hAN hAK hA
    exact false_of_hatK_sym h1332 h1228 S hhat hKf hKM hL1K hL1Z hL1W hhatK hW hTW hZW ho2Z
      F.ρ F.image_L hker F.T_D (hZT w₀ w₀.2 hw₀T) hfix hcount hcL1 hc3 hcW

end CFSG.Quasithin.H13.NQS134
