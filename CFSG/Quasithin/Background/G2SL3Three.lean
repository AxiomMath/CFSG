module

public import CFSG.Quasithin.Background.G2SL3Two
public import CFSG.Quasithin.Background.G2Relaxed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem eq_top_of_two_quotient_odd_index {Γ : Type*} [Group Γ] [Finite Γ] {K M : Subgroup Γ}
    [K.Normal] (hKM : K ≤ M) (h2 : ∀ x : Γ, ∃ k : ℕ, x ^ 2 ^ k ∈ K) (hodd : ¬ 2 ∣ M.index) :
    M = ⊤ := by
  have hP : IsPGroup 2 (Γ ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h2 x
    exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hk⟩
  have hM : (M.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = M := by
    apply Subgroup.comap_map_eq_self
    rw [QuotientGroup.ker_mk']
    exact hKM
  have hidx : (M.map (QuotientGroup.mk' K)).index = M.index := by
    rw [← Subgroup.index_comap_of_surjective (H := M.map (QuotientGroup.mk' K))
      (QuotientGroup.mk'_surjective K), hM]
  obtain ⟨n, hn⟩ := hP.index (M.map (QuotientGroup.mk' K))
  rw [hidx] at hn
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.index_eq_one.1 hn
  · exact absurd (hn ▸ dvd_pow_self 2 n.succ_ne_zero) hodd

theorem AlmostSpecialBase.N_le_H [Finite G] {V V₁ L T H : Subgroup G}
    (hb : AlmostSpecialBase V V₁ L T H) : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ H := by
  set N := L ⊓ Subgroup.normalizer (V₁ : Set G) with hN
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hb.T_le_normL ht, (hb.T_le_normV₁.trans Subgroup.le_normalizer) ht⟩
  have hNL : N ≤ L ⊔ T := inf_le_left.trans le_sup_left
  have hΓ : N ⊔ T ≤ L ⊔ T := sup_le hNL le_sup_right
  set Γ : Subgroup G := N ⊔ T with hΓdef
  have hL₁N : lOne L V₁ ≤ N := oTwoUpper_le N
  have hL₁Γ : lOne L V₁ ≤ Γ := hL₁N.trans le_sup_left
  have hΓn : Γ ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    sup_le (le_normalizer_oTwoUpper N) (hTN.trans (normalizer_le_normalizer_oTwoUpper N))
  have : ((lOne L V₁).subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁Γ).2 hΓn
  have hTΓ : T ≤ Γ := le_sup_right
  have hKM : (lOne L V₁).subgroupOf Γ ≤ (lOne L V₁ ⊔ T).subgroupOf Γ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hx))
  have h2 : ∀ x : ↥Γ, ∃ k : ℕ, x ^ 2 ^ k ∈ (lOne L V₁).subgroupOf Γ := by
    intro x
    obtain ⟨j, hj⟩ := exists_pow_two_pow_mem_of_le_normalizer hTN hb.isPGroup_T x.2
    obtain ⟨i, hi⟩ := exists_pow_mem_oTwoUpper N hj
    refine ⟨j + i, Subgroup.mem_subgroupOf.2 ?_⟩
    have : ((x : G) ^ 2 ^ j) ^ 2 ^ i = (x : G) ^ 2 ^ (j + i) := by
      rw [← pow_mul, ← pow_add]
    rw [Subgroup.coe_pow, ← this]
    exact hi
  have hodd : ¬ 2 ∣ ((lOne L V₁ ⊔ T).subgroupOf Γ).index := by
    intro hd
    have h1 : ((lOne L V₁ ⊔ T).subgroupOf Γ).index ∣ (T.subgroupOf Γ).index :=
      Subgroup.index_dvd_of_le fun x hx =>
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx))
    have h2' : T.relIndex Γ * Γ.relIndex (L ⊔ T) = T.relIndex (L ⊔ T) :=
      Subgroup.relIndex_mul_relIndex T Γ (L ⊔ T) hTΓ hΓ
    apply hb.sylow_LT.2.2
    change 2 ∣ T.relIndex (L ⊔ T)
    rw [← h2']
    exact Dvd.dvd.mul_right (hd.trans h1) _
  have htop := eq_top_of_two_quotient_odd_index hKM h2 hodd
  intro x hx
  have hxΓ : x ∈ Γ := Subgroup.mem_sup_left hx
  have : (⟨x, hxΓ⟩ : ↥Γ) ∈ (lOne L V₁ ⊔ T).subgroupOf Γ := by rw [htop]; exact Subgroup.mem_top _
  exact hb.lOne_sup_le (Subgroup.mem_subgroupOf.1 this)

section Three3

variable {U Sx I : Subgroup G} {g h : G}

theorem comm_mem_P3 (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hgI : g ∈ I) (hhI : h ∈ I)
    (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx)
    (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) :
    I ≤ Subgroup.normalizer ((U ⊓ Sx ⊔ rconj (U ⊓ Sx) g ⊔ rconj (U ⊓ Sx) h : Subgroup G) : Set G) ∧
      ∀ x ∈ I, ∀ s ∈ Sx, x * s * x⁻¹ * s⁻¹ ∈ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g ⊔ rconj (U ⊓ Sx) h := by
  have hUI : U ≤ I := by rw [hI]; exact le_sup_left.trans le_sup_left
  have hUgI : rconj U g ≤ I := by rw [hI]; exact le_sup_right.trans le_sup_left
  have hUhI : rconj U h ≤ I := by rw [hI]; exact le_sup_right
  set P : Subgroup G := U ⊓ Sx ⊔ rconj (U ⊓ Sx) g ⊔ rconj (U ⊓ Sx) h with hP
  have hPSx : P ≤ Sx :=
    sup_le (sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)) (rconj_inf_le_Sx hhI hINorm)
  have hWP : U ⊓ Sx ≤ P := le_sup_left.trans le_sup_left
  have hWgP : rconj (U ⊓ Sx) g ≤ P := le_sup_right.trans le_sup_left
  have hWhP : rconj (U ⊓ Sx) h ≤ P := le_sup_right
  have hgen : ∀ x : G, (x ∈ U ∨ x ∈ rconj U g ∨ x ∈ rconj U h) →
      ∀ s ∈ Sx, x * s * x⁻¹ * s⁻¹ ∈ P := by
    intro x hx s hs
    rcases hx with hx | hx | hx
    · exact hWP (comm_mem_inf_of_normalizes hx hs (fun x hx s hs => hINorm x (hUI hx) s hs) hSxU)
    · exact hWgP (comm_mem_rconj_inf hgI hINorm hUI hSxU hx hs)
    · exact hWhP (comm_mem_rconj_inf hhI hINorm hUI hSxU hx hs)
  have hconj : ∀ x : G, (x ∈ U ∨ x ∈ rconj U g ∨ x ∈ rconj U h) → ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
    intro x hx y hy
    have h1 := hgen x hx y (hPSx hy)
    have := P.mul_mem h1 hy
    simpa [mul_assoc] using this
  have hIP : I ≤ Subgroup.normalizer (P : Set G) := by
    rw [hI]
    exact sup_le (sup_le (le_normalizer_of_conj_mem fun x hx y hy => hconj x (Or.inl hx) y hy)
      (le_normalizer_of_conj_mem fun x hx y hy => hconj x (Or.inr (Or.inl hx)) y hy))
      (le_normalizer_of_conj_mem fun x hx y hy => hconj x (Or.inr (Or.inr hx)) y hy)
  refine ⟨hIP, ?_⟩
  let Z : Subgroup G :=
    { carrier := {x | x ∈ I ∧ ∀ s ∈ Sx, x * s * x⁻¹ * s⁻¹ ∈ P}
      one_mem' := ⟨I.one_mem, fun s _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxI, hx⟩ ⟨hyI, hy⟩
        refine ⟨I.mul_mem hxI hyI, fun s hs => ?_⟩
        have h1 : x * (y * s * y⁻¹ * s⁻¹) * x⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.1 (hIP hxI) _).1 (hy s hs)
        have : x * y * s * (x * y)⁻¹ * s⁻¹ =
            (x * (y * s * y⁻¹ * s⁻¹) * x⁻¹) * (x * s * x⁻¹ * s⁻¹) := by group
        rw [this]
        exact P.mul_mem h1 (hx s hs)
      inv_mem' := by
        rintro x ⟨hxI, hx⟩
        refine ⟨I.inv_mem hxI, fun s hs => ?_⟩
        have h1 : x⁻¹ * (x * s * x⁻¹ * s⁻¹)⁻¹ * x ∈ P := by
          have := (Subgroup.mem_normalizer_iff.1 (hIP (I.inv_mem hxI)) _).1 (P.inv_mem (hx s hs))
          simpa [mul_assoc] using this
        have : x⁻¹ * s * x⁻¹⁻¹ * s⁻¹ = x⁻¹ * (x * s * x⁻¹ * s⁻¹)⁻¹ * x := by group
        rw [this]
        exact h1 }
  have hIZ : I ≤ Z := by
    rw [hI]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact ⟨hUI hx, hgen x (Or.inl hx)⟩
    · intro x hx
      exact ⟨hUgI hx, hgen x (Or.inr (Or.inl hx))⟩
    · intro x hx
      exact ⟨hUhI hx, hgen x (Or.inr (Or.inr hx))⟩
  intro x hx s hs
  exact (hIZ hx).2 s hs

theorem rconj_inf_le_normalizer_rconj_inf {a b : G} (haI : a ∈ I) (hbI : b ∈ I)
    (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx) (hUI : U ≤ I)
    (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) :
    rconj (U ⊓ Sx) a ≤ Subgroup.normalizer (rconj (U ⊓ Sx) b : Set G) := by
  refine le_normalizer_of_conj_mem fun w hw y hy => ?_
  have hwSx : w ∈ Sx := rconj_inf_le_Sx haI hINorm hw
  have hyU : y ∈ rconj U b := by
    have := (Subgroup.mem_inf.1 (mem_rconj.1 hy)).1
    exact mem_rconj.2 this
  have h := comm_mem_rconj_inf hbI hINorm hUI hSxU hyU hwSx
  have e : w * y * w⁻¹ = (y * w * y⁻¹ * w⁻¹)⁻¹ * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h) hy

theorem coe_P3_eq_mul (hgI : g ∈ I) (hhI : h ∈ I) (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx)
    (hUI : U ≤ I) (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) :
    ((U ⊓ Sx ⊔ rconj (U ⊓ Sx) g ⊔ rconj (U ⊓ Sx) h : Subgroup G) : Set G) =
      ((U ⊓ Sx : Subgroup G) : Set G) * (rconj (U ⊓ Sx) g : Set G) *
        (rconj (U ⊓ Sx) h : Set G) := by
  have h1 := W_le_normalizer_rconj hgI hINorm hUI hSxU
  have h2 := W_le_normalizer_rconj hhI hINorm hUI hSxU
  have h3 := rconj_inf_le_normalizer_rconj_inf hgI hhI hINorm hUI hSxU
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (U ⊓ Sx ⊔ rconj (U ⊓ Sx) g) _ (sup_le h2 h3),
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ h1]

end Three3

namespace SL3Model

variable {F : Type*} [Field F]

theorem eq_one_of_smul_basis (A : SL(3, F)) (h0 : A • vE F 0 = vE F 0) (h1 : A • vE F 1 = vE F 1)
    (h2 : A • vE F 2 = vE F 2) : A = 1 := by
  apply Subtype.ext
  ext i j
  have hj : ∀ j : Fin 3, A • (vE F j) = vE F j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have := smul_single_one A j i
  rw [hj j] at this
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, ← this]
  simp [Pi.single_apply]

theorem Qv_inf_Qv_e01 : Qv (vE F 0) ⊓ Qv (vE F 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨⟨h0, hA⟩, ⟨h1, hB⟩⟩
  rw [Subgroup.mem_bot]
  apply eq_one_of_smul_basis A h0 h1
  obtain ⟨c, hc⟩ := hA (vE F 2)
  obtain ⟨c', hc'⟩ := hB (vE F 2)
  have h3 : c • vE F 0 = c' • vE F 1 := add_left_cancel (hc.symm.trans hc')
  have h4 : c = 0 := by simpa [vE] using congrFun h3 0
  rw [hc, h4, zero_smul, add_zero]

theorem Qv_inf_Qv_of_basis {u₁ u₂ u₃ : Fin 3 → F}
    (hspan : ∀ x : Fin 3 → F, ∃ a b c : F, x = a • u₁ + b • u₂ + c • u₃) :
    Qv u₁ ⊓ Qv u₂ = ⊥ := by
  obtain ⟨Q, r, hr, h0, h1, h2⟩ := exists_basis_matrix hspan
  have e : (Qv (vE F 0) ⊓ Qv (vE F 1)).map (MulAut.conj Q).toMonoidHom = Qv u₁ ⊓ Qv u₂ := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj Q).injective, Qv_map_conj, Qv_map_conj, h0, h1]
  rw [← e, Qv_inf_Qv_e01, Subgroup.map_bot]

end SL3Model

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

theorem exists_inf_of_Qv {r : SL(3, GaloisField 2 n)} (hr : r ∈ Qv (vE (GaloisField 2 n) 0)) :
    ∃ x : L, (x : G) ∈ conjClosure V H ∧ S.D.θ x = r := by
  obtain ⟨b, c, rfl⟩ := mem_Qv_e0.1 hr
  have hr' : tq (b + c) b ∈ S.Ubar := by rw [S.Ubar_eq_Qv]; exact tq_mem_Qv _ _
  obtain ⟨u₀, hu₀⟩ := hr'
  obtain ⟨a, ha1, haθ⟩ := S.exists_l1_blk (c3 (GaloisField 2 n)) c3_mem_commutator
  have haH : (a : G) ∈ H :=
    S.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) ha1)
  have haN : (a : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H haH
  have hu₀N : (u₀ : G) ∈ Subgroup.normalizer (L : Set G) := S.U_le_normL u₀.2
  have hxU : (u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ conjClosure V H := by
    have h1 : (a : G) * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.1 haN _).1 (inv_mem u₀.2)
    have := Subgroup.mul_mem _ u₀.2 h1
    simpa [mul_assoc] using this
  have hxL : (u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ L := by
    have h1 : (u₀ : G) * a * (u₀ : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hu₀N _).1 a.2
    exact L.mul_mem h1 (L.inv_mem a.2)
  refine ⟨⟨_, hxL⟩, hxU, ?_⟩
  have hu₀' : (u₀ : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u₀.2
  have ha' : (a : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2
  have e : (⟨(u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹,
      (le_sup_left : L ≤ L ⊔ conjClosure V H) hxL⟩ : ↥(L ⊔ conjClosure V H)) =
      ⟨u₀, hu₀'⟩ * ⟨a, ha'⟩ * ⟨u₀, hu₀'⟩⁻¹ * ⟨a, ha'⟩⁻¹ := Subtype.ext (by simp)
  have h1 := S.Phi_of_L ⟨_, hxL⟩
  rw [← h1, e, map_mul, map_mul, map_mul, map_inv, map_inv]
  have h2 : S.Phi ⟨u₀, hu₀'⟩ = tq (b + c) b := hu₀
  have h3 : S.Phi ⟨a, ha'⟩ = blk (c3 (GaloisField 2 n)) := by rw [S.Phi_of_L a, haθ]
  rw [h2, h3]
  have h4 := tq_mul_blk_c3 (F := GaloisField 2 n) (b + c) b
  have h5 : b + (b + c) = c := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [h5] at h4
  simp only [mul_assoc] at h4 ⊢
  exact h4

theorem exists_inf_rconj_of_Qv {k : G} (hk : k ∈ L) {r : SL(3, GaloisField 2 n)}
    (hr : r ∈ Qv (S.D.θ ⟨k, hk⟩⁻¹ • vE (GaloisField 2 n) 0)) :
    ∃ x : L, (x : G) ∈ rconj (conjClosure V H) k ∧ S.D.θ x = r := by
  set γ := S.D.θ ⟨k, hk⟩⁻¹ with hγ
  have hr' : γ⁻¹ * r * γ ∈ Qv (vE (GaloisField 2 n) 0) :=
    (mem_Qv_conj γ (γ⁻¹ * r * γ)).1 (by simpa [mul_assoc] using hr)
  obtain ⟨x₀, hx₀U, hx₀⟩ := S.exists_inf_of_Qv hr'
  have hxL : k⁻¹ * (x₀ : G) * k ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hk) x₀.2) hk
  refine ⟨⟨k⁻¹ * (x₀ : G) * k, hxL⟩, inv_mul_mul_mem_rconj hx₀U, ?_⟩
  have e : (⟨k⁻¹ * (x₀ : G) * k, hxL⟩ : L) = ⟨k, hk⟩⁻¹ * x₀ * ⟨k, hk⟩ := Subtype.ext (by simp)
  rw [e, map_mul, map_mul, hx₀]
  simp only [hγ, map_inv, inv_inv]
  group

theorem theta_mem_Qv_of_mem_rconj {k : G} (hk : k ∈ L) (b : L)
    (hb : (b : G) ∈ rconj (conjClosure V H) k) :
    S.D.θ b ∈ Qv (S.D.θ ⟨k, hk⟩⁻¹ • vE (GaloisField 2 n) 0) := by
  have hkb : k * (b : G) * k⁻¹ ∈ conjClosure V H := mem_rconj.1 hb
  have hkbL : k * (b : G) * k⁻¹ ∈ L := L.mul_mem (L.mul_mem hk b.2) (L.inv_mem hk)
  have h1 : S.D.θ ⟨k * (b : G) * k⁻¹, hkbL⟩ ∈ Qv (vE (GaloisField 2 n) 0) := by
    rw [← S.Phi_of_L ⟨_, hkbL⟩]
    exact S.betaU_mem_Qv ⟨_, hkb⟩
  have h2 := (mem_Qv_conj (S.D.θ ⟨k, hk⟩⁻¹) _).2 h1
  have e1 : (⟨k * (b : G) * k⁻¹, hkbL⟩ : L) = ⟨k, hk⟩ * b * ⟨k, hk⟩⁻¹ := Subtype.ext (by simp)
  simp only [e1, map_mul, map_inv, inv_inv] at h2
  have e2 : (S.D.θ ⟨k, hk⟩)⁻¹ * (S.D.θ ⟨k, hk⟩ * S.D.θ b * (S.D.θ ⟨k, hk⟩)⁻¹) * S.D.θ ⟨k, hk⟩ =
      S.D.θ b := by group
  rw [map_inv]
  rwa [e2] at h2

theorem inf_pCoreOf_eq_ker {I : Subgroup G} (hI' : I = L ⊔ conjClosure V H) :
    (L ⊓ pCoreOf 2 I).subgroupOf L = S.D.θ.ker := by
  obtain ⟨hIle, hSxO, -, -, -⟩ := sx_facts_gen hI' S.U_le_T S.hyp.base.G22_three.2
    S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  rw [S.D.ker_eq]
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨_, hx⟩
    exact hSxO hx
  · intro hx
    exact ⟨x.2, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI x.2) hx⟩

end L3Setting

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

theorem odd_index_ker_sup3 {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ¬ 2 ∣ (S.D.θ.ker ⊔ (((L ⊓ conjClosure V H) ⊔ (L ⊓ rconj (conjClosure V H) g ⊓
        Subgroup.normalizer (V₁ : Set G))).subgroupOf L)).index := by
  obtain ⟨Q, r, hr, h0, h1, h2⟩ := exists_basis_matrix (S.span_of_sum hg hh hV)
  set C' : Subgroup L := (((L ⊓ conjClosure V H) ⊔ (L ⊓ rconj (conjClosure V H) g ⊓
        Subgroup.normalizer (V₁ : Set G))).subgroupOf L) with hC'
  have hrange : S.D.θ.range = ⊤ := MonoidHom.range_eq_top.2 S.D.surj
  have key := Subgroup.index_map C' S.D.θ
  rw [hrange, Subgroup.index_top, mul_one] at key
  rw [sup_comm, ← key]
  have hle : (Ug (GaloisField 2 n)).map (MulAut.conj Q).toMonoidHom ≤ C'.map S.D.θ := by
    have hU := Ug_conj_le (F := GaloisField 2 n) Q
    rw [h0, h1] at hU
    refine hU.trans (sup_le ?_ ?_)
    · intro A hA
      obtain ⟨x, hxU, hx⟩ := S.exists_inf_of_Qv hA
      exact ⟨x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left ⟨x.2, hxU⟩), hx⟩
    · rintro A ⟨hA2, hA0⟩
      obtain ⟨x, hxU, hx⟩ := S.exists_inf_rconj_of_Qv hg hA2
      have hxN : (x : G) ∈ Subgroup.normalizer (V₁ : Set G) :=
        S.mem_normalizer_V₁_of_stab x (by rw [hx]; exact hA0)
      exact ⟨x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right ⟨⟨x.2, hxU⟩, hxN⟩), hx⟩
  intro hd
  exact Ug_conj_index_odd Q (hd.trans (Subgroup.index_dvd_of_le hle))

theorem inf_inf_C_le {I : Subgroup G} {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) (hI' : I = L ⊔ conjClosure V H) :
    L ⊓ pCoreOf 2 I ⊓ ((L ⊓ conjClosure V H) ⊔ (L ⊓ rconj (conjClosure V H) g ⊓
        Subgroup.normalizer (V₁ : Set G))) ≤
      (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g := by
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.base.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hgI : g ∈ I := hLI hg
  have hB'N : (L ⊓ rconj (conjClosure V H) g ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.normalizer ((L ⊓ conjClosure V H : Subgroup G) : Set G) := by
    intro b hb
    have hbH : b ∈ H := S.hyp.base.toBase.N_le_H ⟨hb.1.1, hb.2⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hb.1.1, le_normalizer_conjClosure V H hbH⟩
  intro z hz
  have hzL : z ∈ L := hz.1.1
  have hzSx : z ∈ pCoreOf 2 I := hz.1.2
  have hzC : z ∈ (L ⊓ conjClosure V H) ⊔ (L ⊓ rconj (conjClosure V H) g ⊓
      Subgroup.normalizer (V₁ : Set G)) := hz.2
  have hmul : (((L ⊓ conjClosure V H) ⊔ (L ⊓ rconj (conjClosure V H) g ⊓
      Subgroup.normalizer (V₁ : Set G)) : Subgroup G) : Set G) =
      ((L ⊓ conjClosure V H : Subgroup G) : Set G) *
        ((L ⊓ rconj (conjClosure V H) g ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
          Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hB'N
  rw [SetLike.mem_coe.symm, hmul] at hzC
  obtain ⟨a, ⟨haL, haU⟩, b, ⟨⟨hbL, hbU⟩, hbN⟩, rfl⟩ := hzC
  have hker : (⟨a * b, hzL⟩ : L) ∈ S.D.θ.ker := by
    rw [S.D.ker_eq]
    exact hSxO hzSx
  rw [MonoidHom.mem_ker] at hker
  have e : (⟨a * b, hzL⟩ : L) = ⟨a, haL⟩ * ⟨b, hbL⟩ := rfl
  rw [e, map_mul] at hker
  have hθa : S.D.θ ⟨a, haL⟩ ∈ Qv (vE (GaloisField 2 n) 0) := by
    rw [← S.Phi_of_L ⟨a, haL⟩]
    exact S.betaU_mem_Qv ⟨a, haU⟩
  have hθb : S.D.θ ⟨b, hbL⟩ ∈ Qv (S.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) :=
    S.theta_mem_Qv_of_mem_rconj hg ⟨b, hbL⟩ hbU
  have hθab : S.D.θ ⟨a, haL⟩ = (S.D.θ ⟨b, hbL⟩)⁻¹ := eq_inv_of_mul_eq_one_left hker
  have hbot := Qv_inf_Qv_of_basis (S.span_of_sum hg hh hV)
  have hθa1 : S.D.θ ⟨a, haL⟩ = 1 := by
    have : S.D.θ ⟨a, haL⟩ ∈ Qv (vE (GaloisField 2 n) 0) ⊓
        Qv (S.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) :=
      ⟨hθa, by rw [hθab]; exact Subgroup.inv_mem _ hθb⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hθb1 : S.D.θ ⟨b, hbL⟩ = 1 := by
    rw [hθa1] at hθab
    exact inv_eq_one.1 hθab.symm
  have haO : a ∈ pCoreOf 2 (L ⊔ T) := by
    have : (⟨a, haL⟩ : L) ∈ S.D.θ.ker := hθa1
    rw [S.D.ker_eq] at this
    exact this
  have hbO : b ∈ pCoreOf 2 (L ⊔ T) := by
    have : (⟨b, hbL⟩ : L) ∈ S.D.θ.ker := hθb1
    rw [S.D.ker_eq] at this
    exact this
  have haSx : a ∈ pCoreOf 2 I := mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI haL) haO
  have hbSx : b ∈ pCoreOf 2 I := mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI hbL) hbO
  have hbW : b ∈ rconj (conjClosure V H ⊓ pCoreOf 2 I) g :=
    mem_rconj.2 ⟨mem_rconj.1 hbU, hINorm g hgI b hbSx⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨haU, haSx⟩) (Subgroup.mem_sup_right hbW)

theorem L_inf_le_P3 {U I : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) :
    L ⊓ pCoreOf 2 I ≤
      (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ⊔ rconj (U ⊓ pCoreOf 2 I) h := by
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G25_two_aux hg hh hV)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.base.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hgI : g ∈ I := hLI hg
  have hhI : h ∈ I := hLI hh
  obtain ⟨hIP, hcomm⟩ := comm_mem_P3 hI hgI hhI hINorm hSxU
  set P := (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g ⊔
    rconj (conjClosure V H ⊓ pCoreOf 2 I) h with hP
  have hPSx : P ≤ pCoreOf 2 I :=
    sup_le (sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)) (rconj_inf_le_Sx hhI hINorm)
  have hWWg : (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g ≤ P :=
    le_sup_left
  refine inf_le_of_central_odd_index S.hyp.base.oTwo_eq hPSx (hLI.trans hIP) ?_
    ((pCoreOf_isPGroup 2 I).to_le inf_le_right) ((S.inf_inf_C_le hg hh hV hI').trans hWWg) ?_
  · intro k hk y hy
    have := P.inv_mem (hcomm y (hLI hy) k hk.2)
    simpa [mul_assoc] using this
  · rw [S.inf_pCoreOf_eq_ker hI']
    exact S.odd_index_ker_sup3 hg hh hV

theorem pCoreOf_I_le_P3 {U I : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) :
    pCoreOf 2 I ≤
      (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ⊔ rconj (U ⊓ pCoreOf 2 I) h := by
  have hL := S.L_inf_le_P3 hU hg hh hV hI
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G25_two_aux hg hh hV)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.base.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  set P := (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g ⊔
    rconj (conjClosure V H ⊓ pCoreOf 2 I) h with hP
  have hWP : conjClosure V H ⊓ pCoreOf 2 I ≤ P := le_sup_left.trans le_sup_left
  have hmul : ((L ⊔ conjClosure V H : Subgroup G) : Set G) =
      (L : Set G) * (conjClosure V H : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ (fun u hu => S.U_le_normL hu)
  intro s hs
  have hsLU : s ∈ L ⊔ conjClosure V H := hI' ▸ pCoreOf_le 2 I hs
  rw [SetLike.mem_coe.symm, hmul] at hsLU
  obtain ⟨l, hl, u, hu, rfl⟩ := hsLU
  change l * u ∈ pCoreOf 2 I at hs
  show l * u ∈ P
  have hlLU : l ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hl
  have huLU : u ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have hsLU : l * u ∈ L ⊔ conjClosure V H := Subgroup.mul_mem _ hlLU huLU
  have h1 : S.Phi ⟨l * u, hsLU⟩ = 1 := (S.Phi_eq_one_iff _).2 (hSxO hs)
  have e : (⟨l * u, hsLU⟩ : ↥(L ⊔ conjClosure V H)) = ⟨l, hlLU⟩ * ⟨u, huLU⟩ := rfl
  rw [e, map_mul, S.Phi_of_L ⟨l, hl⟩] at h1
  have h2 : S.Phi ⟨u, huLU⟩ = S.betaU ⟨u, hu⟩ := rfl
  rw [h2] at h1
  have hlθ : S.D.θ ⟨l, hl⟩ = (S.betaU ⟨u, hu⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hlQ : S.D.θ ⟨l, hl⟩ ∈ Qv (vE (GaloisField 2 n) 0) := by
    rw [hlθ]
    exact Subgroup.inv_mem _ (S.betaU_mem_Qv _)
  obtain ⟨x, hxU, hx⟩ := S.exists_inf_of_Qv hlQ
  have hkL : l * (x : G)⁻¹ ∈ L := L.mul_mem hl (L.inv_mem x.2)
  have hkker : (⟨l * (x : G)⁻¹, hkL⟩ : L) ∈ S.D.θ.ker := by
    rw [MonoidHom.mem_ker]
    have e2 : (⟨l * (x : G)⁻¹, hkL⟩ : L) = ⟨l, hl⟩ * x⁻¹ := Subtype.ext (by simp)
    rw [e2, map_mul, map_inv, hx, mul_inv_cancel]
  have hkO : l * (x : G)⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
    have := hkker
    rw [S.D.ker_eq] at this
    exact this
  have hkSx : l * (x : G)⁻¹ ∈ pCoreOf 2 I :=
    mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI hkL) hkO
  have hkP : l * (x : G)⁻¹ ∈ P := hL ⟨hkL, hkSx⟩
  have hwU : (x : G) * u ∈ conjClosure V H := Subgroup.mul_mem _ hxU hu
  have hwSx : (x : G) * u ∈ pCoreOf 2 I := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hkSx) hs
    have e3 : (l * (x : G)⁻¹)⁻¹ * (l * u) = (x : G) * u := by group
    rwa [e3] at this
  have hwP : (x : G) * u ∈ P := hWP ⟨hwU, hwSx⟩
  have e4 : l * u = (l * (x : G)⁻¹) * ((x : G) * u) := by group
  rw [e4]
  exact P.mul_mem hkP hwP

theorem pCoreOf_I_eq3 {U I : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) :
    pCoreOf 2 I =
        (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ⊔ rconj (U ⊓ pCoreOf 2 I) h ∧
      ((pCoreOf 2 I : Subgroup G) : Set G) =
        ((U ⊓ pCoreOf 2 I : Subgroup G) : Set G) * (rconj (U ⊓ pCoreOf 2 I) g : Set G) *
          (rconj (U ⊓ pCoreOf 2 I) h : Set G) := by
  have hle := S.pCoreOf_I_le_P3 hU hg hh hV hI
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G25_two_aux hg hh hV)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.base.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hUI : conjClosure V H ≤ I := hI' ▸ le_sup_right
  have hgI : g ∈ I := hLI hg
  have hhI : h ∈ I := hLI hh
  have heq : pCoreOf 2 I =
      (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g ⊔
        rconj (conjClosure V H ⊓ pCoreOf 2 I) h :=
    le_antisymm hle
      (sup_le (sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)) (rconj_inf_le_Sx hhI hINorm))
  refine ⟨heq, ?_⟩
  conv_lhs => rw [heq]
  exact coe_P3_eq_mul hgI hhI hINorm hUI hSxU

end L3Setting

namespace AlmostSpecialL3Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL3Hyp n V V₁ L T H)

include hyp

theorem G25_three {U I S W : Subgroup G} (hU : U = conjClosure V H) {g h : G} (hg : g ∈ L)
    (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hI : I = U ⊔ rconj U g ⊔ rconj U h) (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    S = W ⊔ rconj W g ⊔ rconj W h ∧
      (S : Set G) = (W : Set G) * (rconj W g : Set G) * (rconj W h : Set G) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n V V₁ L T H := ⟨hyp, D⟩
  subst hS
  subst hW
  exact St.pCoreOf_I_eq3 hU hg hh hV hI

end AlmostSpecialL3Hyp

end CFSG.Quasithin
