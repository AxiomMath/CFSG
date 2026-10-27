module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenCommutator

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_ne_bot_of_two_groups {A W : Subgroup G} (hA : IsPGroup 2 A)
    (hW : IsPGroup 2 W) (hAW : A ≤ normalizer (W : Set G)) (hWne : W ≠ ⊥) :
    W ⊓ centralizer (A : Set G) ≠ ⊥ := by
  set R : Subgroup G := A ⊔ W with hRdef
  have hR2 : IsPGroup 2 R := hA.to_sup_of_normal_right' hW hAW
  have hWR : W ≤ R := le_sup_right
  have hRN : R ≤ normalizer (W : Set G) := sup_le hAW (Subgroup.le_normalizer (H := W))
  haveI hNormal : (W.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hRN
  have hWne' : W.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hWne
    have h := congrArg (Subgroup.map R.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le hWR, Subgroup.map_bot] at h
    exact h
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥R) (H := W.subgroupOf R) hWne'
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hzW : ((z : ↥R) : G) ∈ W := Subgroup.mem_subgroupOf.mp z.2.1
  have hzC : ((z : ↥R) : G) ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haR : a ∈ R := Subgroup.mem_sup_left ha
    have hcomm := Subgroup.mem_center_iff.mp z.2.2 (⟨a, haR⟩ : ↥R)
    exact congrArg Subtype.val hcomm
  intro hbot
  have hmem : ((z : ↥R) : G) ∈ W ⊓ centralizer (A : Set G) := Subgroup.mem_inf.mpr ⟨hzW, hzC⟩
  rw [hbot] at hmem
  have hz1' : ((z : ↥R) : G) = 1 := Subgroup.mem_bot.mp hmem
  exact hz1 (Subtype.ext (by simpa using hz1'))

section Sit

variable {V H T A L K : Subgroup G} {i : ℕ}

theorem Sit813.eGrp_le_omegaOneCenterOf (h : Sit813 V H T i A L K) :
    eGrp H T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  have hH : IsCalH V H := h.calH0.1
  have hT := h.minCex.hyp.sylow
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hO2T : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
  have hC : omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
    intro c hc
    have hcT : c ∈ T := omegaOneCenterOf_le T hc
    have hcC : ∀ y ∈ T, y * c = c * y := fun y hy => mem_centralizer_of_mem_omegaOneCenterOf hc hy
    have hcCen : c ∈ centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => hcC y (hO2T hy)
    have hcO2 : c ∈ pCoreOf 2 H := hH.2.1 ⟨hTH.le hcT, hcCen⟩
    exact mem_omegaOneCenterOf hcO2 (fun y hy => hcC y (hO2T hy))
      ((B2F.isElemAbelian_omegaOneCenterOf T).2 c hc)
  unfold eGrp
  refine conjClosure_le fun x hx c hc => ?_
  have hHnorm : H ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H).trans
      (normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H))
  exact (Subgroup.mem_normalizer_iff.mp (hHnorm hx) c).1 (hC hc)

theorem Sit813.isElemAbelian_eGrp (h : Sit813 V H T i A L K) : IsElemAbelian 2 (eGrp H T) :=
  CFSG.Open.IsElemAbelian.mono (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 H))
    h.eGrp_le_omegaOneCenterOf

theorem Sit813.k_le_H (h : Sit813 V H T i A L K) : K ≤ H :=
  h.concl813.sub_L.trans h.concl813.comp.2.2.1

theorem Sit813.T_le_H (h : Sit813 V H T i A L K) : T ≤ H :=
  (isSylowIn_of_isCalH h.calH0.1 h.minCex.hyp.sylow).le

theorem Sit813.le_normalizer_eGrp (h : Sit813 V H T i A L K) :
    H ≤ normalizer (eGrp H T : Set G) :=
  le_normalizer_conjClosure _ _

theorem Sit813.pCoreOf_le_cGrp (h : Sit813 V H T i A L K) : pCoreOf 2 H ≤ cGrp H T := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨CFSG.openPCoreOf_le 2 H hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact (mem_centralizer_of_mem_omegaOneCenterOf (h.eGrp_le_omegaOneCenterOf he) hx).symm

theorem Sit813.pCoreOf_le_rGrp (h : Sit813 V H T i A L K) : pCoreOf 2 H ≤ rGrp H T K := by
  intro t ht
  rw [Sit813.mem_rGrp_iff]
  refine ⟨pCoreOf_le_of_isCalH h.calH0.1 h.minCex.hyp.sylow ht,
    Subgroup.le_normalizer (h.concl813.ge_C (h.pCoreOf_le_cGrp ht)), fun k hk => ?_⟩
  have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H (h.k_le_H hk)
  have h1 : k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp hnorm t⁻¹).1 ((pCoreOf 2 H).inv_mem ht)
  have h2 : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
  rw [h2]
  exact h.cGrp_le_oTwoMod (h.pCoreOf_le_cGrp ((pCoreOf 2 H).mul_mem ht h1))

theorem Sit813.uGrp_le_pCoreOf (h : Sit813 V H T i A L K) : uGrp V K ≤ pCoreOf 2 H := by
  have hVO : V ≤ pCoreOf 2 H := h.calH0.2
  unfold uGrp
  refine conjClosure_le fun k hk v hv => ?_
  have hnorm := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H) (h.k_le_H hk)
  exact (Subgroup.mem_normalizer_iff.mp hnorm v).1 (hVO hv)

theorem mem_normalizer_centralizer_of_mem_normalizer_set {K : Subgroup G} {t : G}
    (ht : t ∈ normalizer (K : Set G)) : t ∈ normalizer (centralizer (K : Set G) : Set G) := by
  have key : ∀ s ∈ normalizer (K : Set G), ∀ x ∈ centralizer (K : Set G),
      s * x * s⁻¹ ∈ centralizer (K : Set G) := by
    intro s hs x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : s⁻¹ * k * s ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem hs) k).1 hk
      simpa using this
    have h1 : (s⁻¹ * k * s) * x = x * (s⁻¹ * k * s) := Subgroup.mem_centralizer_iff.mp hx _ hk'
    calc k * (s * x * s⁻¹) = s * ((s⁻¹ * k * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * k * s)) * s⁻¹ := by rw [h1]
      _ = (s * x * s⁻¹) * k := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key t ht x, fun hx => by
    have := key t⁻¹ ((normalizer (K : Set G)).inv_mem ht) _ hx
    simpa [mul_assoc] using this⟩

theorem Sit813.inf_normalizer_le_sup (h : Sit813 V H T i A L K) {X : Subgroup G}
    (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G))) :
    K ⊓ normalizer (V : Set G) ≤ (T ⊓ K) ⊔ oTwoMod (cGrp H T) K ⊔ X := by
  set K₁ : Subgroup G := K ⊓ normalizer (V : Set G) with hK₁
  set N : Subgroup G := oTwoMod (cGrp H T) K with hN
  set W : Subgroup G := (T ⊓ K) ⊔ N ⊔ X with hW
  have hNK₁ : N ≤ K₁ := h.oTwoMod_le_inf
  have hTK₁ : T ⊓ K ≤ K₁ := le_inf inf_le_right (inf_le_left.trans h.le_normalizer_T)
  have hWK₁ : W ≤ K₁ := sup_le (sup_le hTK₁ hNK₁) hX.le
  have hNW : N ≤ W := le_sup_right.trans le_sup_left
  have hTW : T ⊓ K ≤ W := le_sup_left.trans le_sup_left
  have hXW : X ≤ W := le_sup_right
  have hK₁K : K₁ ≤ K := inf_le_left
  have hWK : W ≤ K := hWK₁.trans hK₁K
  have h1 : W.relIndex K₁ * K₁.relIndex K = W.relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ hWK₁ hK₁K
  have h3 : (T ⊓ K).relIndex W * W.relIndex K = (T ⊓ K).relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ hTW hWK
  have h4 : N.relIndex K₁ * K₁.relIndex K = N.relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ hNK₁ hK₁K
  have h6 : N.relIndex W * W.relIndex K₁ = N.relIndex K₁ :=
    Subgroup.relIndex_mul_relIndex _ _ _ hNW hWK₁
  have h7 : X.relIndex W * W.relIndex K₁ = X.relIndex K₁ :=
    Subgroup.relIndex_mul_relIndex _ _ _ hXW hWK₁
  have hd5 : K₁.relIndex K = 5 := h.concl813.d_index
  have hn60 : N.relIndex K = 60 := h.kn4
  have hodd : ¬ 2 ∣ (T ⊓ K).relIndex K := h.concl813.t_sylow.not_dvd_relIndex
  have h3X : ¬ 3 ∣ X.relIndex K₁ := hX.not_dvd_relIndex
  rw [hd5] at h1 h4
  rw [hn60] at h4
  have hK₁N : N.relIndex K₁ = 12 := by omega
  rw [hK₁N] at h6
  have hm12 : W.relIndex K₁ ∣ 12 := ⟨N.relIndex W, by rw [← h6]; ring⟩
  have hm2 : ¬ 2 ∣ W.relIndex K₁ := by
    intro hdv
    apply hodd
    rw [← h3]
    obtain ⟨c, hc⟩ := hdv
    exact ⟨(T ⊓ K).relIndex W * (5 * c), by rw [← h1, hc]; ring⟩
  have hm3 : ¬ 3 ∣ W.relIndex K₁ := by
    intro hdv
    apply h3X
    rw [← h7]
    exact Dvd.dvd.mul_left hdv _
  have hm1 : W.relIndex K₁ = 1 := by
    have hle : W.relIndex K₁ ≤ 12 := Nat.le_of_dvd (by norm_num) hm12
    have hpos : 0 < W.relIndex K₁ := Nat.pos_of_dvd_of_pos hm12 (by norm_num)
    generalize W.relIndex K₁ = m at hle hpos hm2 hm3 hm12 ⊢
    interval_cases m <;> omega
  exact Subgroup.relIndex_eq_one.mp hm1

theorem mem_zpowers_involution_iff_eq_one_or_eq {w : G} (hw2 : w * w = 1) (x : G) :
    x ∈ Subgroup.zpowers w ↔ x = 1 ∨ x = w := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hw2' : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw2
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · left
      rw [← hn, zpow_mul, hw2', one_zpow]
    · right
      rw [← hn, zpow_add, zpow_mul, hw2', one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem Sit813.centralizes_of_fixed (h : Sit813 V H T i A L K) {w : G} (hw1 : w ≠ 1)
    (hw2 : w * w = 1) (hwE : w ∈ eGrp H T) (hwT : ∀ t ∈ T, t * w = w * t)
    (hfix : ∀ k ∈ K ⊓ normalizer (V : Set G), k * w = w * k) :
    ∀ k ∈ K, k * w = w * k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k₀, hk₀K, hk₀⟩ := hcon
  set W : Subgroup G := Subgroup.zpowers w with hW
  have hmemW := mem_zpowers_involution_iff_eq_one_or_eq hw2
  have hnormW : ∀ g : G, g ∈ normalizer (W : Set G) ↔ g * w = w * g := by
    intro g
    constructor
    · intro hg
      have h1 : g * w * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hg w).1 (Subgroup.mem_zpowers w)
      rcases (hmemW _).mp h1 with h2 | h2
      · exfalso
        apply hw1
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      · calc g * w = (g * w * g⁻¹) * g := by group
          _ = w * g := by rw [h2]
    · intro hg
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      have hgw : g * w * g⁻¹ = w := by rw [hg]; group
      rcases (hmemW _).mp hn with rfl | rfl
      · simpa using W.one_mem
      · rw [hgw]
        exact hn
  have hK₁ : K ⊓ normalizer (W : Set G) = K ⊓ normalizer (V : Set G) := by
    have hge : K ⊓ normalizer (V : Set G) ≤ K ⊓ normalizer (W : Set G) := fun k hk =>
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hk).1,
        (hnormW k).mpr (hfix k hk)⟩
    have hmul : (K ⊓ normalizer (V : Set G)).relIndex (K ⊓ normalizer (W : Set G)) *
        (K ⊓ normalizer (W : Set G)).relIndex K = (K ⊓ normalizer (V : Set G)).relIndex K :=
      Subgroup.relIndex_mul_relIndex _ _ _ hge inf_le_left
    rw [h.concl813.d_index] at hmul
    have hne : (K ⊓ normalizer (W : Set G)).relIndex K ≠ 1 := by
      intro h1
      have hle : K ≤ K ⊓ normalizer (W : Set G) := Subgroup.relIndex_eq_one.mp h1
      exact hk₀ (((hnormW k₀).mp (Subgroup.mem_inf.mp (hle hk₀K)).2))
    have hdvd : (K ⊓ normalizer (V : Set G)).relIndex (K ⊓ normalizer (W : Set G)) ∣ 5 :=
      ⟨_, hmul.symm⟩
    have h1 : (K ⊓ normalizer (V : Set G)).relIndex (K ⊓ normalizer (W : Set G)) = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hmul
        omega
    exact le_antisymm (fun g hg => by
      have hg' : g ∈ K ⊓ normalizer (V : Set G) := Subgroup.relIndex_eq_one.mp h1 hg
      exact hg') hge
  have hKH : K ≤ H := h.k_le_H
  have hTH : T ≤ H := h.T_le_H
  have D0 := h.fiveData
  have D : Five.FiveData W K (oTwoMod (cGrp H T) K) T (rGrp H T K) A (eGrp H T) :=
    { setup := by rw [hK₁]; exact D0.setup
      ti := by
        intro g hg v hv hgv
        rcases (hmemW _).mp hv with rfl | rfl
        · rfl
        · exfalso
          apply hg
          rw [hnormW]
          rcases (hmemW _).mp hgv with h2 | h2
          · exfalso
            apply hw1
            calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
              _ = 1 := by rw [h2]; group
          · calc g * v = (g * v * g⁻¹) * g := by group
              _ = v * g := by rw [h2]
      a_card := D0.a_card
      a_sq := D0.a_sq
      a_comm := D0.a_comm
      a_le_T := D0.a_le_T
      a_normV := fun a ha => (hnormW a).mpr (hwT a (D0.a_le_T ha))
      a_normK := D0.a_normK
      r_le_T := D0.r_le_T
      r_comm := D0.r_comm
      inf_le_R := D0.inf_le_R
      decomp := fun a ha => by rw [hK₁]; exact D0.decomp a ha
      alpha := D0.alpha
      u_comm := fun x hx y hy => h.isElemAbelian_eGrp.comm hx hy
      u_sq := fun x hx => h.isElemAbelian_eGrp.mul_self_eq_one hx
      u_normK := hKH.trans h.le_normalizer_eGrp
      u_normA := (h.mem.1.trans hTH).trans h.le_normalizer_eGrp
      u_gen := fun k hk v hv =>
        (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_eGrp (hKH hk)) v).1
          ((Subgroup.zpowers_le.mpr hwE) hv)
      u_cent := (eight_thirteen_faithful h.minCex.hyp.hyp7 h.calH0 h.minCex.hyp.sylow h.mem
        h.notLe).2 }
  obtain ⟨a, haA, w', hw', hne⟩ := Five.five_conjugates D (v := w) (Subgroup.mem_zpowers w) hw1
    (fun k hk => by
      have hk' : k ∈ K ⊓ normalizer (V : Set G) := by rw [← hK₁]; exact hk
      calc k * w * k⁻¹ = (w * k) * k⁻¹ := by rw [hfix k hk']
        _ = w := by group)
  have haw : a * w = w * a := hwT a (h.mem.1 haA)
  rcases (hmemW _).mp hw' with rfl | rfl
  · exact hne (by simp)
  · exact hne haw

end Sit

end CFSG.LocalAnalysis.WeakClosure81

end
