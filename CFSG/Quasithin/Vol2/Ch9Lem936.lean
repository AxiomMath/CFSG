module

public import CFSG.Quasithin.Vol2.Ch9Lem934
public import CFSG.Quasithin.Vol2.Ch9Sec3Red

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {D : Subgroup G}

theorem le_sup_L (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) :
    D ≤ (D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) ⊔ L := by
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) :=
    le_sup_right.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c)
  have hyL : ∀ y (hy : y ∈ D), ψ ⟨y, hDL hy⟩ ∈ (L.subgroupOf (fsuL0 T L)).map ψ → y ∈ L := by
    intro y hy hψy
    obtain ⟨⟨l, hlL0⟩, hl, hψl⟩ := hψy
    have hq := hc.mem_Q_of_psi_eq_one h37c h38c (⟨l, hlL0⟩⁻¹ * ⟨y, hDL hy⟩) (by
      rw [map_mul, map_inv, hψl, inv_mul_cancel])
    have hle : Subgroup.zpowers y ≤ Q ⊔ L := by
      rw [Subgroup.zpowers_le]
      have e' : y = l * (l⁻¹ * y) := by group
      rw [e']
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hl))
        (Subgroup.mem_sup_left hq)
    have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
      rw [Nat.card_zpowers]
      exact hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hy)
    exact Vol2.Ch10.SecB.C11AmS.le_of_odd hle hodd
      (B6.isTwoQuotient_of_sup_eq S.isPGroup_Q (sup_le hQL Subgroup.le_normalizer) rfl)
      (Subgroup.mem_zpowers y)
  intro x hx
  obtain ⟨a, b, hab⟩ := exists_diag_of_mem hdiag hx (hDL hx)
  rcases hc.map_L h37c h38c with hL | hL
  · obtain ⟨b', hb'D, hb'L, hψb'⟩ := exists_mem_of_diag hdiag b⁻¹ b
    have hb'B := (hc.mem_centralizer_V1_iff_diag ⟨b', hb'L⟩ b⁻¹ b hψb').mpr (inv_mul_cancel b)
    have hy : b'⁻¹ * x ∈ L := hyL _ (D.mul_mem (D.inv_mem hb'D) hx) (by
      rw [hL]
      have e' : (⟨b'⁻¹ * x, hDL (D.mul_mem (D.inv_mem hb'D) hx)⟩ : ↥(fsuL0 T L)) =
          ⟨b', hb'L⟩⁻¹ * ⟨x, hDL hx⟩ := rfl
      rw [MonoidHom.mem_ker, e', map_mul, map_inv, hψb', hab]
      simp)
    have e' : x = b' * (b'⁻¹ * x) := by group
    rw [e']
    exact mul_mem (Subgroup.mem_sup_left ⟨hb'D, hb'B⟩) (Subgroup.mem_sup_right hy)
  · obtain ⟨b', hb'D, hb'L, hψb'⟩ := exists_mem_of_diag hdiag a a⁻¹
    have hb'B := (hc.mem_centralizer_V1_iff_diag ⟨b', hb'L⟩ a a⁻¹ hψb').mpr (mul_inv_cancel a)
    have hy : b'⁻¹ * x ∈ L := hyL _ (D.mul_mem (D.inv_mem hb'D) hx) (by
      rw [hL]
      have e' : (⟨b'⁻¹ * x, hDL (D.mul_mem (D.inv_mem hb'D) hx)⟩ : ↥(fsuL0 T L)) =
          ⟨b', hb'L⟩⁻¹ * ⟨x, hDL hx⟩ := rfl
      rw [MonoidHom.mem_ker, e', map_mul, map_inv, hψb', hab]
      simp)
    have e' : x = b' * (b'⁻¹ * x) := by group
    rw [e']
    exact mul_mem (Subgroup.mem_sup_left ⟨hb'D, hb'B⟩) (Subgroup.mem_sup_right hy)

theorem V1_le_of_mem (h2 : n = 2)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) {X : Subgroup G}
    (hDX : D ≤ Subgroup.normalizer (X : Set G)) {w : G}
    (hwV : w ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G))
    (hw1 : w ≠ 1) (hwX : w ∈ X) :
    fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤ X := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hcoord : ∀ {u : G} (hu : u ∈ fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G)), e ⟨u, hu.1⟩ = Multiplicative.ofAdd
        ((Multiplicative.toAdd (e ⟨u, hu.1⟩) 0 0) • !![(1 : K), 0; 0, 0]) := by
    intro u hu
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact hc.toAdd_e_eq hu
  intro v hv
  set c := (Multiplicative.toAdd (e ⟨v, hv.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hcdef
  set c₀ := (Multiplicative.toAdd (e ⟨w, hwV.1⟩) : Matrix (Fin 2) (Fin 2) K) 0 0 with hc₀def
  have hev := hcoord hv
  have hew := hcoord hwV
  rw [← hcdef] at hev
  rw [← hc₀def] at hew
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    apply hw1
    have h3 : e ⟨w, hwV.1⟩ = 1 := by rw [hew, h0, zero_smul]; rfl
    exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h3)
  by_cases hc0 : c = 0
  · have hv1 : v = 1 := by
      have h3 : e ⟨v, hv.1⟩ = 1 := by rw [hev, hc0, zero_smul]; rfl
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h3)
    rw [hv1]
    exact X.one_mem
  set q := Units.mk0 (c / c₀) (div_ne_zero hc0 hc₀) with hq
  obtain ⟨d, hdD, hdL, hψd⟩ := exists_mem_of_diag hdiag (q ^ 2) (q ^ 2)
  have hq4 : ((q ^ 2 : Kˣ) : K) * ((q ^ 2 : Kˣ) : K) = c / c₀ := by
    have h3 := pow_three_eq_one_of_card_four hK4 q
    have : (q ^ 2) * (q ^ 2) = q := by
      calc q ^ 2 * q ^ 2 = q ^ 3 * q := by group
        _ = q := by rw [h3, one_mul]
    rw [← Units.val_mul, this, hq, Units.val_mk0]
  have h3 : bar e (Subgroup.inclusion S.L0_le_normalizer_V ⟨d, hdL⟩) (e ⟨w, hwV.1⟩) =
      e ⟨v, hv.1⟩ := by
    rw [hc.bar_L0, hψd, hew, rho_diag_smul_e11, hev, hq4, div_mul_cancel₀ c hc₀]
  rw [bar_apply] at h3
  have h4 : d * w * d⁻¹ = v := congrArg Subtype.val (e.injective h3)
  rw [← h4]
  exact (Subgroup.mem_normalizer_iff.mp (hDX hdD) w).mp hwX

end IsCoord

variable (S : Setup T L I n)
include S

theorem lem936 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3108 : Stmt3_2_10_eight) (h2 : n = 2) (h1 : zQ T I = fsuV T I) {K D K₀ : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hM₀M : ¬ L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤ fsuM T L)
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀) :
    L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K =
        K₀ ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ∧
      fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤
        pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ∧
      CharTwo (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set O := pCoreOf 2 M₀ with hO
  have hLM₀ : L ≤ M₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hDM₀ : D ≤ M₀ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hT₁M₀ : T₁ ≤ M₀ := le_sup_right.trans le_sup_left
  have hK₀M₀ : K₀ ≤ M₀ := le_of_mem_cComp hK₀
  have hM₀N : M₀ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀
  have hOT₁ : O ≤ T₁ := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hDK₀ : D ≤ K₀ := (hc.le_sup_L h37 h38 h37c h38c hD hdiag).trans
    (sup_le (hBK.trans hKK₀) hLK₀)
  have hM₀eq : M₀ = K₀ ⊔ T₁ := le_antisymm
    (sup_le (sup_le (sup_le (hLK₀.trans le_sup_left) (hDK₀.trans le_sup_left)) le_sup_right)
      (hKK₀.trans le_sup_left)) (sup_le hK₀M₀ hT₁M₀)
  have hT₁2 : IsPGroup 2 T₁ := hfsu.sylow.1.to_le inf_le_left
  have hW := CFSG.QuasithinUnique.inf_centralizer_ne_bot_of_normalizes hT₁2 hOT₁
    (hT₁M₀.trans hM₀N) hM₀O
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hO2.to_le (inf_le_left : O ⊓ _ ≤ O))
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hW (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
  obtain ⟨⟨w, hwW⟩, hw2⟩ := exists_prime_orderOf_dvd_card' 2
    (show 2 ∣ Nat.card ↥(O ⊓ Subgroup.centralizer (T₁ : Set G)) by
      rw [hk]; exact dvd_pow_self 2 hk0)
  have hw2' : w ^ 2 = 1 := by
    have h3 := pow_orderOf_eq_one (⟨w, hwW⟩ : ↥(O ⊓ Subgroup.centralizer (T₁ : Set G)))
    rw [hw2] at h3
    exact congrArg Subtype.val h3
  have hw1 : w ≠ 1 := by
    intro h0
    have h3 : (⟨w, hwW⟩ : ↥(O ⊓ Subgroup.centralizer (T₁ : Set G))) = 1 := Subtype.ext h0
    rw [h3, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hQT₁ : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ T₁ :=
    le_inf inf_le_left (le_sup_right.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hwZ : w ∈ omegaOneCenterOf T₁ :=
    Subgroup.subset_closure ⟨⟨hOT₁ hwW.1, hwW.2⟩, hw2'⟩
  have hwV := S.omegaOneCenter_le h1 hQT₁ inf_le_left hwZ
  have hTL₀T₁ : T ⊓ fsuL0 T L ≤ T₁ :=
    le_inf inf_le_left (le_sup_left.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hwV₁ : w ∈ V₁ := ⟨hwV.1, Subgroup.centralizer_le hTL₀T₁ hwV.2⟩
  have hV₁O : V₁ ≤ O := hc.V1_le_of_mem h2 hdiag (hDM₀.trans hM₀N) hwV₁ hw1 hwW.1
  have hTsyl : IsSylowTwoOf T ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow le_top
  have hZ := S.omegaOneCenter_T_le h1
  have hZ1 : quasithinOmegaOneCenter T ≠ ⊥ := by
    obtain ⟨z, hzV, hzZ, c, hc0, hze⟩ := hc.exists_z h1
    intro h0
    rw [h0, Subgroup.mem_bot] at hzZ
    apply hc0
    have h3 : e ⟨z, hzV⟩ = 1 := by
      rw [show (⟨z, hzV⟩ : ↥(fsuV T I)) = 1 from Subtype.ext hzZ, map_one]
    rw [hze] at h3
    have h4 := congrArg
      (fun X : Om4.VM F => (Multiplicative.toAdd X : Matrix (Fin 2) (Fin 2) F) 0 0) h3
    simpa using h4
  have hOZ : O ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro h0
    apply hZ1
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ O ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨hV₁O (hZ hz), (Subgroup.closure_le _).mpr (fun x hx => hx.1) hz⟩
    rw [h0] at hz'
    exact hz'
  have hNchar : CharTwo (Subgroup.normalizer (O : Set G)) :=
    charTwo_normalizer_of_inf_center hfsu.qtke.2.1 hTsyl hO2 hOZ
  have hON : O ≤ pCoreOf 2 (Subgroup.normalizer (O : Set G)) :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl hO2
  have hNsyl := S.lem934 h37 h38 h37c h38c h3108 (hLM₀.trans hM₀N) (hT₁M₀.trans hM₀N)
    (fun h0 => hM₀O (le_bot_iff.mp (h0 ▸ hON))) (fun h => hM₀M (hM₀N.trans h))
  have hONT₁ : pCoreOf 2 (Subgroup.normalizer (O : Set G)) ≤ T₁ :=
    F7.isSylowTwoOf_pCoreOf_le hNsyl
  refine ⟨hM₀eq, hV₁O, charTwo_of_pCore_centralizer_le hNchar hM₀N ?_⟩
  exact inf_le_left.trans (hONT₁.trans hT₁M₀)

end Setup

end CFSG.Quasithin.H13.Ch9
