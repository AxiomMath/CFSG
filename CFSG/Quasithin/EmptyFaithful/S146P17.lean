module

public import CFSG.Quasithin.EmptyFaithful.S146P14
public import CFSG.Quasithin.EmptyFaithful.S146P16
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.S14612DB
public import CFSG.Quasithin.EmptyFaithful.S146F20

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Finite3

theorem rot_pow_exists_P17 : ∀ i j : ZMod 3, i ≠ 0 →
    ∃ n : ℕ, n < 3 ∧ (DihedralGroup.r i : DihedralGroup 3) ^ n = DihedralGroup.r j := by
  decide

theorem refl_conj_P17 (k i : ZMod 3) :
    (DihedralGroup.sr k : DihedralGroup 3) * DihedralGroup.r i * (DihedralGroup.sr k)⁻¹ *
      DihedralGroup.r i = 1 := by
  revert k i; decide

theorem rot_conj_P17 (k i : ZMod 3) :
    (DihedralGroup.r k : DihedralGroup 3) * DihedralGroup.r i * (DihedralGroup.r k)⁻¹ *
      (DihedralGroup.r i)⁻¹ = 1 := by
  revert k i; decide

theorem rot_sq_P17 (i : ZMod 3)
    (h : (DihedralGroup.r i : DihedralGroup 3) * DihedralGroup.r i = 1) : i = 0 := by
  revert i h; decide

end Finite3

section DihPack

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.dihPack_P17 (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ 3)
    (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    ∃ a ∈ oTwoUpper H₁, ∃ s ∈ (T ⊓ H₀) ⊓ H₁, a ^ 3 = 1 ∧ a ∉ pCoreOf 2 H ∧ s ∉ pCoreOf 2 H ∧
      (∀ y ∈ oTwoUpper H₁, ∃ n : ℕ, y * (a ^ n)⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ c ∈ H₁, c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 H ∨ c * a * c⁻¹ * a ∈ pCoreOf 2 H) ∧
      s * a * s⁻¹ * a ∈ pCoreOf 2 H := by
  obtain ⟨φ, -, hker⟩ := h.exists_phi
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hrot : ∀ y ∈ oTwoUpper H₁, ∃ hyH : y ∈ H₁, ∃ i : ZMod 3,
      φ ⟨y, hyH⟩ = DihedralGroup.r i := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyH, hyodd⟩ := hy
      refine ⟨hyH, ?_⟩
      cases hφ : φ ⟨y, hyH⟩ with
      | r i => exact ⟨i, rfl⟩
      | sr i =>
        exfalso
        have hdvd : orderOf (φ ⟨y, hyH⟩) ∣ orderOf y := by
          have := orderOf_map_dvd φ (⟨y, hyH⟩ : ↥H₁)
          rwa [← Subgroup.orderOf_coe] at this
        rw [hφ, DihedralGroup.orderOf_sr] at hdvd
        have := hyodd.of_dvd_nat hdvd
        exact absurd this (by decide)
    | one =>
      refine ⟨H₁.one_mem, 0, ?_⟩
      have : (⟨1, H₁.one_mem⟩ : ↥H₁) = 1 := rfl
      rw [this, map_one]
      exact DihedralGroup.r_zero.symm
    | mul y z _ _ ihy ihz =>
      obtain ⟨hyH, i, hi⟩ := ihy
      obtain ⟨hzH, j, hj⟩ := ihz
      refine ⟨H₁.mul_mem hyH hzH, i + j, ?_⟩
      have : (⟨y * z, H₁.mul_mem hyH hzH⟩ : ↥H₁) = ⟨y, hyH⟩ * ⟨z, hzH⟩ := rfl
      rw [this, map_mul, hi, hj, DihedralGroup.r_mul_r]
    | inv y _ ih =>
      obtain ⟨hyH, i, hi⟩ := ih
      refine ⟨H₁.inv_mem hyH, -i, ?_⟩
      have : (⟨y⁻¹, H₁.inv_mem hyH⟩ : ↥H₁) = (⟨y, hyH⟩ : ↥H₁)⁻¹ := rfl
      rw [this, map_inv, hi]
      exact DihedralGroup.inv_r i
  obtain ⟨a, haX, hao⟩ := h.exists_order_p_P14 (p := 3) Nat.prime_three (by norm_num)
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have haQ : a ∉ pCoreOf 2 H := by
    intro haQ
    obtain ⟨k, hk⟩ := hQ2 ⟨a, haQ⟩
    have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hao] at hd
    have : 3 ∣ 2 ^ k := hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  obtain ⟨haH, i₀, hi₀⟩ := hrot a haX
  have hi₀ne : i₀ ≠ 0 := by
    intro h0
    apply haQ
    apply (hker ⟨a, haH⟩).mp
    rw [hi₀, h0, DihedralGroup.r_zero]
  obtain ⟨hS₁, hQS, hidx⟩ := h.isSylowTwoOf_inf_H₁ S hred
  obtain ⟨s, hs, hsQ⟩ := exists_mem_not_mem_of_relIndex_two hidx
  have hsH₁ : s ∈ H₁ := hs.2
  have hss : s * s ∈ pCoreOf 2 H := by
    have hs'Q : s⁻¹ ∉ pCoreOf 2 H := fun hh => hsQ (by simpa using (pCoreOf 2 H).inv_mem hh)
    have := mul_inv_mem_of_relIndex_two hidx hs (((T ⊓ H₀) ⊓ H₁).inv_mem hs) hsQ hs'Q
    simpa using this
  have hφs1 : φ ⟨s, hsH₁⟩ ≠ 1 := fun hh => hsQ ((hker _).mp hh)
  have hφss : φ ⟨s, hsH₁⟩ * φ ⟨s, hsH₁⟩ = 1 := by
    rw [← map_mul]
    exact (hker _).mpr hss
  obtain ⟨k, hk⟩ : ∃ k : ZMod 3, φ ⟨s, hsH₁⟩ = DihedralGroup.sr k := by
    cases hφ : φ ⟨s, hsH₁⟩ with
    | r i =>
      exfalso
      rw [hφ] at hφss hφs1
      exact hφs1 (by rw [rot_sq_P17 i hφss, DihedralGroup.r_zero])
    | sr k => exact ⟨k, rfl⟩
  refine ⟨a, haX, s, hs, ha3, haQ, hsQ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hyH, j, hj⟩ := hrot y hy
    obtain ⟨n, -, hn⟩ := rot_pow_exists_P17 i₀ j hi₀ne
    refine ⟨n, ?_⟩
    have h1 : φ (⟨y, hyH⟩ * (⟨a, haH⟩ ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hj, hi₀, hn, mul_inv_cancel]
    have := (hker _).mp h1
    simpa using this
  · intro c hc
    cases hφc : φ ⟨c, hc⟩ with
    | r k' =>
      left
      have h1 : φ (⟨c, hc⟩ * ⟨a, haH⟩ * ⟨c, hc⟩⁻¹ * ⟨a, haH⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφc, hi₀]
        exact rot_conj_P17 k' i₀
      have := (hker _).mp h1
      simpa using this
    | sr k' =>
      right
      have h1 : φ (⟨c, hc⟩ * ⟨a, haH⟩ * ⟨c, hc⟩⁻¹ * ⟨a, haH⟩) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, hφc, hi₀]
        exact refl_conj_P17 k' i₀
      have := (hker _).mp h1
      simpa using this
  · have h1 : φ (⟨s, hsH₁⟩ * ⟨a, haH⟩ * ⟨s, hsH₁⟩⁻¹ * ⟨a, haH⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hk, hi₀]
      exact refl_conj_P17 k i₀
    have := (hker _).mp h1
    simpa using this

end DihPack

section Sub

variable {G : Type} [Group G] [Finite G]

theorem core_sub_P16 {G₁ K R T₀ : Subgroup G} {a₁ a₂ s₁ s₂ x : G}
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥G₁) ≤ 2)
    (hKG : K ≤ G₁) (hT₀G : T₀ ≤ G₁) (hR2 : IsPGroup 2 ↥R)
    (hRn : ∀ g ∈ G₁, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hRK : R ≤ K)
    (hKn : ∀ g ∈ G₁, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hT₀2 : IsPGroup 2 ↥T₀)
    (ha₁K : a₁ ∈ K) (ha₂K : a₂ ∈ K) (ha₁3 : a₁ ^ 3 = 1) (ha₂3 : a₂ ^ 3 = 1)
    (ha₁R : a₁ ∉ R) (ha₂R : a₂ ∉ R) (hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ R)
    (hinf : ∀ m n : ℤ, a₁ ^ m * (a₂ ^ n)⁻¹ ∈ R → a₁ ^ m ∈ R)
    (hgen : ∀ k ∈ K, ∃ m n : ℤ, k * (a₁ ^ m * a₂ ^ n)⁻¹ ∈ R)
    (hT₀a₁ : ∀ τ ∈ T₀, ∃ n : ℤ, τ * a₁ * τ⁻¹ * (a₁ ^ n)⁻¹ ∈ R)
    (hT₀a₂ : ∀ τ ∈ T₀, ∃ n : ℤ, τ * a₂ * τ⁻¹ * (a₂ ^ n)⁻¹ ∈ R)
    (hs₁ : s₁ ∈ T₀) (hs₁a₁ : s₁ * a₁ * s₁⁻¹ * a₁ ∈ R) (hs₁a₂ : s₁ * a₂ * s₁⁻¹ * a₂⁻¹ ∈ R)
    (hs₂ : s₂ ∈ T₀) (hs₂a₁ : s₂ * a₁ * s₂⁻¹ * a₁⁻¹ ∈ R) (hs₂a₂ : s₂ * a₂ * s₂⁻¹ * a₂ ∈ R)
    (hxG : x ∈ G₁) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxT₀ : ∀ τ ∈ T₀, x * τ * x⁻¹ ∈ T₀) (hxT₀' : ∀ τ ∈ T₀, x⁻¹ * τ * x ∈ T₀) : False := by
  have hmem : ∀ (S : Subgroup G) (y : ↥G₁), y ∈ S.subgroupOf G₁ ↔ (y : G) ∈ S :=
    fun S y => Subgroup.mem_subgroupOf
  refine core_P16 (Y := ↥G₁) (K := K.subgroupOf G₁) (R := R.subgroupOf G₁)
    (T₀ := T₀.subgroupOf G₁) (a₁ := ⟨a₁, hKG ha₁K⟩) (a₂ := ⟨a₂, hKG ha₂K⟩)
    (s₁ := ⟨s₁, hT₀G hs₁⟩) (s₂ := ⟨s₂, hT₀G hs₂⟩) (x := ⟨x, hxG⟩) hrank
    (hR2.comap_of_injective G₁.subtype G₁.subtype_injective)
    (fun g r hr => (hmem R _).mpr (by simpa using hRn _ g.2 _ ((hmem R r).mp hr)))
    (fun r hr => (hmem K r).mpr (hRK ((hmem R r).mp hr)))
    (fun g k hk => (hmem K _).mpr (by simpa using hKn _ g.2 _ ((hmem K k).mp hk)))
    ((hmem K _).mpr ha₁K) ((hmem K _).mpr ha₂K)
    (Subtype.ext (by simpa using ha₁3)) (Subtype.ext (by simpa using ha₂3))
    (fun h => ha₁R ((hmem R _).mp h)) (fun h => ha₂R ((hmem R _).mp h))
    ((hmem R _).mpr (by simpa using hcomm))
    (fun m n h => (hmem R _).mpr (by
      simpa using hinf m n (by simpa using (hmem R _).mp h)))
    (fun k hk => by
      obtain ⟨m, n, hmn⟩ := hgen k ((hmem K k).mp hk)
      exact ⟨m, n, (hmem R _).mpr (by simpa using hmn)⟩)
    (fun τ hτ => by
      obtain ⟨n, hn⟩ := hT₀a₁ τ ((hmem T₀ τ).mp hτ)
      exact ⟨n, (hmem R _).mpr (by simpa using hn)⟩)
    (fun τ hτ => by
      obtain ⟨n, hn⟩ := hT₀a₂ τ ((hmem T₀ τ).mp hτ)
      exact ⟨n, (hmem R _).mpr (by simpa using hn)⟩)
    ((hmem T₀ _).mpr hs₁) ((hmem R _).mpr (by simpa using hs₁a₁))
    ((hmem R _).mpr (by simpa using hs₁a₂))
    ((hmem T₀ _).mpr hs₂) ((hmem R _).mpr (by simpa using hs₂a₁))
    ((hmem R _).mpr (by simpa using hs₂a₂))
    (Subtype.ext (by simpa using hx3)) (fun h => hx1 (by simpa using congrArg Subtype.val h))
    (fun τ hτ => (hmem T₀ _).mpr (by simpa using hxT₀ _ ((hmem T₀ τ).mp hτ)))
    (fun τ hτ => (hmem T₀ _).mpr (by simpa using hxT₀' _ ((hmem T₀ τ).mp hτ)))
    (hT₀2.comap_of_injective G₁.subtype G₁.subtype_injective)

end Sub

section Main

variable {G : Type} [Group G] [Finite G]

theorem input14616One_proved : Input14616One := by
  intro G _ _ T M S H PQ p hred hp3 hC1 H₀ H₁ H₂ t hdec
  subst hp3
  have hdecP : IsDecP T M H 3 H₀ H₁ H₂ t := hdec.toIsDecP hred
  have hdecP' : IsDecP T M H 3 H₀ H₂ H₁ t⁻¹ := hdecP.swap
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₀H : H₀ ≤ H := hdec.le
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hH₀H
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hH₀H
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKG : oTwoUpper H ≤ mcOf T := hKH.trans hHG
  have hKn : ∀ g ∈ mcOf T, ∀ k ∈ oTwoUpper H, g * k * g⁻¹ ∈ oTwoUpper H := by
    intro g hg k hk
    have := mem_conjClosure hg hk
    rwa [hC1.1] at this
  have hKH' : ∀ g ∈ H, ∀ k ∈ oTwoUpper H, g * k * g⁻¹ ∈ oTwoUpper H := fun g hg k hk =>
    hKn g (hHG hg) k hk
  have hRK : pCoreOf 2 (oTwoUpper H) ≤ oTwoUpper H := pCoreOf_le 2 _
  have hR2 : IsPGroup 2 (pCoreOf 2 (oTwoUpper H)) := pCoreOf_isPGroup 2 _
  have hRn : ∀ g ∈ mcOf T, ∀ r ∈ pCoreOf 2 (oTwoUpper H), g * r * g⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    intro g hg r hr
    have hgK : g ∈ Subgroup.normalizer (oTwoUpper H : Set G) :=
      S146A.le_normalizer_of_forall_conj_mem (L := mcOf T) (K := oTwoUpper H) hKn hg
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H) hgK) r).mp hr
  have hRQ : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hRK.trans hKH)
      ((le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H))) hR2
  have hKQR : ∀ c ∈ oTwoUpper H, c ∈ pCoreOf 2 H → c ∈ pCoreOf 2 (oTwoUpper H) := by
    intro c hcK hcQ
    have hn : oTwoUpper H ≤ Subgroup.normalizer ((oTwoUpper H ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      S146A.le_normalizer_of_forall_conj_mem fun g hg x hx =>
        ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem hg hx.1) ((oTwoUpper H).inv_mem hg),
          hQn g (hKH hg) x hx.2⟩
    have hle : oTwoUpper H ⊓ pCoreOf 2 H ≤ pCoreOf 2 (oTwoUpper H) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hn (hQ2.to_le inf_le_right)
    exact hle ⟨hcK, hcQ⟩
  obtain ⟨a₁, ha₁X, s₁, hs₁S, ha₁3, ha₁Q, hs₁Q, hpow₁, hconj₁, hrefl₁⟩ := hdecP.dihPack_P17 S hred
  obtain ⟨a₂, ha₂X, s₂, hs₂S, ha₂3, ha₂Q, hs₂Q, hpow₂, hconj₂, hrefl₂⟩ := hdecP'.dihPack_P17 S hred
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdecP.oTwoUpper_eq S hred
  have ha₁K : a₁ ∈ oTwoUpper H := by rw [hKX]; exact Subgroup.mem_sup_left ha₁X
  have ha₂K : a₂ ∈ oTwoUpper H := by rw [hKX]; exact Subgroup.mem_sup_right ha₂X
  have ha₁H₁ : a₁ ∈ H₁ := oTwoUpper_le H₁ ha₁X
  have ha₂H₂ : a₂ ∈ H₂ := oTwoUpper_le H₂ ha₂X
  have hcommQ : ∀ {u v : G}, u ∈ H₁ → v ∈ H₂ → u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 H := fun {u v} hu hv =>
    hdecP.comm (Subgroup.commutator_mem_commutator hu hv)
  have hcommQ' : ∀ {u v : G}, u ∈ H₂ → v ∈ H₁ → u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 H := fun {u v} hu hv => by
    refine hdecP.comm ?_
    rw [← Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu hv
  have hmemK : ∀ {g c : G}, g ∈ H → c ∈ oTwoUpper H → g * c * g⁻¹ ∈ oTwoUpper H := fun {g c} hg hc =>
    hKH' g hg c hc
  have hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    refine hKQR _ ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ha₁K ha₂K)
      ((oTwoUpper H).inv_mem ha₁K)) ((oTwoUpper H).inv_mem ha₂K)) (hcommQ ha₁H₁ ha₂H₂)
  have hinf : ∀ m n : ℤ, a₁ ^ m * (a₂ ^ n)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) →
      a₁ ^ m ∈ pCoreOf 2 (oTwoUpper H) := by
    intro m n h
    have h1 : a₁ ^ m * (a₂ ^ n)⁻¹ ∈ pCoreOf 2 H := hRQ h
    have hm : a₁ ^ m ∈ H₁ := H₁.zpow_mem ha₁H₁ m
    have hn : a₂ ^ n ∈ H₂ := H₂.zpow_mem ha₂H₂ n
    have e : a₁ ^ m = (a₁ ^ m * (a₂ ^ n)⁻¹) * a₂ ^ n := by group
    have h2 : a₁ ^ m ∈ H₂ := by
      rw [e]
      exact H₂.mul_mem (hdecP.Q₂ h1) hn
    have h3 : a₁ ^ m ∈ pCoreOf 2 H := by
      rw [← hdecP.inf]
      exact ⟨hm, h2⟩
    exact hKQR _ ((oTwoUpper H).zpow_mem ha₁K m) h3
  have hgen : ∀ k ∈ oTwoUpper H, ∃ m n : ℤ,
      k * (a₁ ^ m * a₂ ^ n)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    intro k hk
    have hn₁₂ : oTwoUpper H₁ ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := fun y hy =>
      normalizer_le_normalizer_oTwoUpper_P (hdecP.H₁_le_normalizer_H₂ (oTwoUpper_le H₁ hy))
    have hmul : ((oTwoUpper H₁ ⊔ oTwoUpper H₂ : Subgroup G) : Set G) =
        ((oTwoUpper H₁ : Subgroup G) : Set G) * ((oTwoUpper H₂ : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn₁₂
    have hk' : k ∈ ((oTwoUpper H₁ ⊔ oTwoUpper H₂ : Subgroup G) : Set G) := by rw [← hKX]; exact hk
    rw [hmul] at hk'
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_mul.mp hk'
    obtain ⟨n₁, hn₁⟩ := hpow₁ y₁ hy₁
    obtain ⟨n₂, hn₂⟩ := hpow₂ y₂ hy₂
    refine ⟨(n₁ : ℤ), (n₂ : ℤ), ?_⟩
    rw [zpow_natCast, zpow_natCast]
    have hy₁K : y₁ ∈ oTwoUpper H := by rw [hKX]; exact Subgroup.mem_sup_left hy₁
    have hy₂K : y₂ ∈ oTwoUpper H := by rw [hKX]; exact Subgroup.mem_sup_right hy₂
    have hu : a₁ ^ n₁ ∈ oTwoUpper H := (oTwoUpper H).pow_mem ha₁K n₁
    have hv : a₂ ^ n₂ ∈ oTwoUpper H := (oTwoUpper H).pow_mem ha₂K n₂
    have hr₁ : y₁ * (a₁ ^ n₁)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
      hKQR _ ((oTwoUpper H).mul_mem hy₁K ((oTwoUpper H).inv_mem hu)) hn₁
    have hr₂ : y₂ * (a₂ ^ n₂)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
      hKQR _ ((oTwoUpper H).mul_mem hy₂K ((oTwoUpper H).inv_mem hv)) hn₂
    have e : y₁ * y₂ * (a₁ ^ n₁ * a₂ ^ n₂)⁻¹ =
        (y₁ * (a₁ ^ n₁)⁻¹) * ((a₁ ^ n₁) * (y₂ * (a₂ ^ n₂)⁻¹) * (a₁ ^ n₁)⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 (oTwoUpper H)).mul_mem hr₁ (hRn _ (hKG hu) _ hr₂)
  have hT₀H₀ : T ⊓ Subgroup.normalizer (H₁ : Set G) = T ⊓ H₀ := hdec.inf_normalizer_eq hTH
  have conjGen : ∀ (A B : Subgroup G) (t' : G), IsDecP T M H 3 H₀ A B t' → ∀ a ∈ A,
      a ∈ oTwoUpper H → (∀ c ∈ A, c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 H ∨ c * a * c⁻¹ * a ∈ pCoreOf 2 H) →
      ∀ τ ∈ H₀, ∃ n : ℤ, τ * a * τ⁻¹ * (a ^ n)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    intro A B t' hD a haA haK hconj τ hτ
    have hAH : A ≤ H := hD.le₁.trans hD.le
    have hBH : B ≤ H := hD.le₂.trans hD.le
    have hmul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A B hD.H₁_le_normalizer_H₂
    have hτ' : τ ∈ ((A ⊔ B : Subgroup G) : Set G) := by rw [← hD.sup]; exact hτ
    rw [hmul] at hτ'
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := Set.mem_mul.mp hτ'
    have hc₂Q : h₂ * a * h₂⁻¹ * a⁻¹ ∈ pCoreOf 2 H := by
      have := hD.comm (Subgroup.commutator_mem_commutator haA hh₂)
      have h1 : a * h₂ * a⁻¹ * h₂⁻¹ ∈ pCoreOf 2 H := this
      have := (pCoreOf 2 H).inv_mem h1
      have e : (a * h₂ * a⁻¹ * h₂⁻¹)⁻¹ = h₂ * a * h₂⁻¹ * a⁻¹ := by group
      rwa [e] at this
    have hc₂K : h₂ * a * h₂⁻¹ * a⁻¹ ∈ oTwoUpper H :=
      (oTwoUpper H).mul_mem (hmemK (hBH hh₂) haK) ((oTwoUpper H).inv_mem haK)
    have hc₂ : h₂ * a * h₂⁻¹ * a⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := hKQR _ hc₂K hc₂Q
    have hc₂' : h₁ * (h₂ * a * h₂⁻¹ * a⁻¹) * h₁⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
      hRn _ (hHG (hAH hh₁)) _ hc₂
    have haK' : h₁ * a * h₁⁻¹ ∈ oTwoUpper H := hmemK (hAH hh₁) haK
    rcases hconj h₁ hh₁ with hc | hc
    · refine ⟨1, ?_⟩
      have e : h₁ * h₂ * a * (h₁ * h₂)⁻¹ * (a ^ (1 : ℤ))⁻¹ =
          (h₁ * (h₂ * a * h₂⁻¹ * a⁻¹) * h₁⁻¹) * (h₁ * a * h₁⁻¹ * a⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 (oTwoUpper H)).mul_mem hc₂'
        (hKQR _ ((oTwoUpper H).mul_mem haK' ((oTwoUpper H).inv_mem haK)) hc)
    · refine ⟨-1, ?_⟩
      have e : h₁ * h₂ * a * (h₁ * h₂)⁻¹ * (a ^ (-1 : ℤ))⁻¹ =
          (h₁ * (h₂ * a * h₂⁻¹ * a⁻¹) * h₁⁻¹) * (h₁ * a * h₁⁻¹ * a) := by group
      rw [e]
      exact (pCoreOf 2 (oTwoUpper H)).mul_mem hc₂'
        (hKQR _ ((oTwoUpper H).mul_mem haK' haK) hc)
  have hT₀a₁ : ∀ τ ∈ T ⊓ Subgroup.normalizer (H₁ : Set G), ∃ n : ℤ,
      τ * a₁ * τ⁻¹ * (a₁ ^ n)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := fun τ hτ =>
    conjGen H₁ H₂ t hdecP a₁ ha₁H₁ ha₁K hconj₁ τ (by rw [hT₀H₀] at hτ; exact hτ.2)
  have hT₀a₂ : ∀ τ ∈ T ⊓ Subgroup.normalizer (H₁ : Set G), ∃ n : ℤ,
      τ * a₂ * τ⁻¹ * (a₂ ^ n)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := fun τ hτ =>
    conjGen H₂ H₁ t⁻¹ hdecP' a₂ ha₂H₂ ha₂K hconj₂ τ (by rw [hT₀H₀] at hτ; exact hτ.2)
  have hs₁H₁ : s₁ ∈ H₁ := hs₁S.2
  have hs₂H₂ : s₂ ∈ H₂ := hs₂S.2
  have hs₁T₀ : s₁ ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) :=
    ⟨hs₁S.1.1, Subgroup.le_normalizer hs₁H₁⟩
  have hs₂T₀ : s₂ ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) :=
    ⟨hs₂S.1.1, hdecP.H₂_le_normalizer_H₁ hs₂H₂⟩
  have hs₁a₁ : s₁ * a₁ * s₁⁻¹ * a₁ ∈ pCoreOf 2 (oTwoUpper H) :=
    hKQR _ ((oTwoUpper H).mul_mem (hmemK (hH₁H hs₁H₁) ha₁K) ha₁K) hrefl₁
  have hs₂a₂ : s₂ * a₂ * s₂⁻¹ * a₂ ∈ pCoreOf 2 (oTwoUpper H) :=
    hKQR _ ((oTwoUpper H).mul_mem (hmemK (hH₂H hs₂H₂) ha₂K) ha₂K) hrefl₂
  have hs₁a₂ : s₁ * a₂ * s₁⁻¹ * a₂⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
    hKQR _ ((oTwoUpper H).mul_mem (hmemK (hH₁H hs₁H₁) ha₂K) ((oTwoUpper H).inv_mem ha₂K))
      (hcommQ hs₁H₁ ha₂H₂)
  have hs₂a₁ : s₂ * a₁ * s₂⁻¹ * a₁⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    refine hKQR _ ((oTwoUpper H).mul_mem (hmemK (hH₂H hs₂H₂) ha₁K) ((oTwoUpper H).inv_mem ha₁K)) ?_
    have h1 : a₁ * s₂ * a₁⁻¹ * s₂⁻¹ ∈ pCoreOf 2 H := by
      have := hcommQ ha₁H₁ hs₂H₂
      exact this
    have := (pCoreOf 2 H).inv_mem h1
    have e : (a₁ * s₂ * a₁⁻¹ * s₂⁻¹)⁻¹ = s₂ * a₁ * s₂⁻¹ * a₁⁻¹ := by group
    rwa [e] at this
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxN : (x' : G) ∈ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) ⊓
      mcOf T := oTwoUpper_le _ x'.2
  have hxo : orderOf (x' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx'
  have hx3 : (x' : G) ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  have hx1 : (x' : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(mcOf T)) ≤ 2 :=
    (S.sqtkGroup_of_isHTM S.isHTM_mcOf).1 3 Nat.prime_three (by norm_num)
  have hT₀G : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ mcOf T := inf_le_left.trans (hTH.trans hHG)
  refine core_sub_P16 (G₁ := mcOf T) (K := oTwoUpper H) (R := pCoreOf 2 (oTwoUpper H))
    (T₀ := T ⊓ Subgroup.normalizer (H₁ : Set G)) (a₁ := a₁) (a₂ := a₂) (s₁ := s₁) (s₂ := s₂)
    (x := (x' : G)) hrank hKG hT₀G hR2 hRn hRK hKn (hT2.to_le inf_le_left) ha₁K ha₂K ha₁3 ha₂3
    (fun h => ha₁Q (hRQ h)) (fun h => ha₂Q (hRQ h)) hcomm hinf hgen hT₀a₁ hT₀a₂ hs₁T₀ hs₁a₁ hs₁a₂
    hs₂T₀ hs₂a₁ hs₂a₂ hxN.2 hx3 hx1 ?_ ?_
  · intro τ hτ
    exact (Subgroup.mem_normalizer_iff.mp hxN.1 τ).mp hτ
  · intro τ hτ
    refine (Subgroup.mem_normalizer_iff.mp hxN.1 _).mpr ?_
    have e : (x' : G) * ((x' : G)⁻¹ * τ * (x' : G)) * (x' : G)⁻¹ = τ := by group
    rw [e]
    exact hτ

end Main

end CFSG.Quasithin
