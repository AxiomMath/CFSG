module

public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.Quasithin.H13.NQCatT3Inv
public import CFSG.Quasithin.H13.NQCatT3Lat
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.Quasithin.EmptyFaithful.S146zYFSJ2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.Sporadic.J2
public import Certificates.Certificate7161

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Blueprint CFSG.Quasithin.E2P.SporB
open scoped Pointwise

theorem mem_normalizer_of_map_mem {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {K : Subgroup G} {x : G}
    (hx : f x ∈ Subgroup.normalizer ((K.map f : Subgroup H) : Set H)) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  have := Subgroup.le_normalizer_comap f
    (show x ∈ (Subgroup.normalizer ((K.map f : Subgroup H) : Set H)).comap f from hx)
  rwa [Subgroup.comap_map_eq_self_of_injective hf] at this

theorem j2_overgroup
    {Z : Subgroup ↥CFSG.Sporadic.J2.J} (hSZ : j2Ctx.S ≤ Z) :
    Z = ⊤ ∨ ∃ j < 5, Z = j2Ctx.Y j ∧ Nat.card ↥Z = #[1, 3, 9, 15, 3][j]! * 2 ^ 7 := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  obtain ⟨j, hj, hZ⟩ := lat_all j2Ctx hL Z hSZ
  by_cases hj5 : j < 5
  · have hY : Z = j2Ctx.Y j := by
      rw [hZ]
      exact list_member (L := #[1, 3, 9, 15, 3]) hj5
    have hk : j2Ctx.k = 7 := rfl
    refine Or.inr ⟨j, hj5, hY, ?_⟩
    rw [hY, lat_card j2Ctx hL j hj5, hk]
  · left
    have h5 : j = 5 := by
      have : j ≤ 5 := hj
      omega
    rw [hZ]
    unfold memberOrTop
    rw [ite_eq_right (by simp [h5])]

theorem j2_not_normal
    (hc : J2T3K.notNormal) :
    ¬ j2Ctx.Y 4 ≤ Subgroup.normalizer (j2Ctx.S : Set ↥CFSG.Sporadic.J2.J) := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  exact not_le_normalizer_of_label j2Ctx (by rw [lat_J_eq j2Ctx hL]; decide) hc

theorem j2_Y1_le_Y3
    (hc : J2T3K.incl) : j2Ctx.Y 1 ≤ j2Ctx.Y 3 := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hJ : j2Ctx.J = 5 := lat_J_eq j2Ctx hL
  exact j2Ctx.gensIn_le (by rw [hJ]; decide) (by rw [hJ]; decide) hc

theorem mem_normalizer_of_lattice {Γ P : Type} [Group Γ] [Finite Γ] [Group P] [Finite P]
    (φ : P ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) (hS₀c : Nat.card ↥S₀ = 2 ^ 7)
    {Y : ℕ → Subgroup Γ}
    (hover : ∀ Z : Subgroup Γ, S₀ ≤ Z →
      Z = ⊤ ∨ ∃ j < 5, Z = Y j ∧ Nat.card ↥Z = #[1, 3, 9, 15, 3][j]! * 2 ^ 7)
    (hY4 : ¬ Y 4 ≤ Subgroup.normalizer (S₀ : Set Γ)) (hY13 : Y 1 ≤ Y 3)
    (hΓ : Nat.card Γ = 604800) {T : Subgroup P} (hT2 : IsPGroup 2 ↥T) (hTi : ¬ 2 ∣ T.index)
    {x : P} (hxo : orderOf x = 3)
    (hperm : ∀ t ∈ T, ∀ y ∈ Subgroup.zpowers x, ∃ y' ∈ Subgroup.zpowers x, ∃ t' ∈ T,
      t * y = y' * t')
    (hxN : x ∈ Subgroup.normalizer (T : Set P)) {R₁ : Subgroup P}
    (hTR : T ≤ Subgroup.normalizer (R₁ : Set P)) (h5 : 5 ∣ Nat.card ↥R₁) :
    x ∈ Subgroup.normalizer (R₁ : Set P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let US : Sylow 2 Γ := hS₀.2.1.toSylow (by
    have := hS₀.2.2
    have e : (S₀.subgroupOf ⊤).index = S₀.index := Subgroup.relIndex_top_right _
    rwa [e] at this)
  let TS : Sylow 2 Γ := (hT2.toSylow hTi).mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ TS US
  have hST : S₀ = (T.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have h1 : (US : Subgroup Γ) = S₀ := rfl
    rw [← h1, ← hg, Sylow.coe_subgroup_smul]
    rfl
  have hTc : Nat.card T = 2 ^ 7 := by
    rwa [hST, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective φ.injective] at hS₀c
  have hY : Nat.card ↥(Subgroup.zpowers x ⊔ T) = 3 * 2 ^ 7 := by
    rw [card_sup_of_perm hperm (by rw [Nat.card_zpowers, hxo, hTc]; norm_num), Nat.card_zpowers,
      hxo, hTc]
  set Y' := ((Subgroup.zpowers x ⊔ T).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom
    with hY'
  have hSY : S₀ ≤ Y' := by
    rw [hST]
    exact Subgroup.map_mono (Subgroup.map_mono le_sup_right)
  have hYc : Nat.card Y' = 3 * 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective φ.injective, hY]
  have hYN : Y' ≤ Subgroup.normalizer (S₀ : Set Γ) := by
    rw [hST]
    refine (Subgroup.map_mono (Subgroup.map_mono
      (sup_le (Subgroup.zpowers_le.mpr hxN) Subgroup.le_normalizer))).trans ?_
    exact (Subgroup.map_mono (Subgroup.le_normalizer_map _)).trans (Subgroup.le_normalizer_map _)
  have hY1 : Y' = Y 1 := by
    rcases hover Y' hSY with htop | ⟨j, hj, hYj, hcj⟩
    · rw [htop, Subgroup.card_top, hΓ] at hYc
      norm_num at hYc
    · rw [hYc] at hcj
      have hj14 : j = 1 ∨ j = 4 := by
        revert hcj
        interval_cases j <;> decide
      rcases hj14 with rfl | rfl
      · exact hYj
      · exact (hY4 (hYj ▸ hYN)).elim
  set R' := (R₁.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom with hR'
  have hSR' : S₀ ≤ Subgroup.normalizer (R' : Set Γ) := by
    rw [hST]
    exact (Subgroup.map_mono ((Subgroup.map_mono hTR).trans
      (Subgroup.le_normalizer_map _))).trans (Subgroup.le_normalizer_map _)
  have h5' : 5 ∣ Nat.card R' := by
    rwa [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective φ.injective]
  have hY1Z : Y 1 ≤ R' ⊔ S₀ := by
    rcases hover (R' ⊔ S₀) le_sup_right with htop | ⟨j, hj, hZj, hcj⟩
    · rw [htop]
      exact le_top
    · have h5Z : 5 ∣ Nat.card ↥(R' ⊔ S₀) := h5'.trans (Subgroup.card_dvd_of_le le_sup_left)
      rw [hcj] at h5Z
      have hj3 : j = 3 := by
        revert h5Z
        interval_cases j <;> decide
      subst hj3
      rw [hZj]
      exact hY13
  have hxY : (MulAut.conj g).toMonoidHom (φ.toMonoidHom x) ∈ Y 1 := by
    rw [← hY1]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
  exact mem_normalizer_of_map_mem φ.injective (mem_normalizer_of_map_mem
    (MulAut.conj g).injective (sup_le Subgroup.le_normalizer hSR' (hY1Z hxY)))

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_j2
    (h : Star513 Q R S B D)
    (hQ : IsSporadic .J2 ↥Q)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A))
    (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A)) :
    (∀ d ∈ D, d ^ 3 ∈ Subgroup.centralizer (Q : Set A)) ∧
      ∃ t ∈ S ⊓ Q, ∀ d ∈ D, t * d * t⁻¹ * d ∈ Subgroup.centralizer (Q : Set A) := by
  obtain ⟨hnn, hincl⟩ : J2T3K.stmt := Certificates.certificate7161
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  have : Finite NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  have hc2 : Subgroup.center NativeSporadic.J2 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center NativeSporadic.J2) with
      hz | hz
    · exact hz
    · have : IsMulCommutative NativeSporadic.J2 := Subgroup.center_eq_top_iff.mp hz
      have hp := Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup NativeSporadic.J2)
      rw [CFSG.Sporadic.J2.card_J2] at hp
      rcases hp.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2 <;> omega
  obtain ⟨e₀⟩ := hQ
  have hM : Group.IsPerfect NativeSporadic.J2 := isPerfect_of_center_eq_bot hc2
  have hZ : Subgroup.center ↥Q = ⊥ := by
    have h1 := Subgroup.map_center_eq (G := ↥Q) (H := NativeSporadic.J2) e₀
    rw [hc2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).mp h1
  let ψ' := (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₀)
  let ψ := ψ'.trans CFSG.Sporadic.J2.nativeEquiv
  have : Finite (↥Q ⧸ Subgroup.center ↥Q) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hperf : Group.IsPerfect ↥Q := Group.IsPerfect.ofSurjective (G := NativeSporadic.J2)
    (G' := ↥Q) (f := e₀.symm.toMonoidHom) e₀.symm.surjective
  have hQperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hperf
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ :=
    @Group.IsPerfect.center_quotient_center_eq_bot ↥Q _ hperf
  have hA : Nat.card (MulAut NativeSporadic.J2) = 1209600 :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.1
  have hinn := oddInner_of_mulEquiv ψ' (oddInner_of_card_le (G := NativeSporadic.J2) hc2 (by
    norm_num [hA, CFSG.Sporadic.J2.card_J2]))
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨x, hx, k, hxk⟩ := iPart_eq_zpowers e hcen hinn h hD3
  have hx3 : x ^ 3 = 1 := by
    have hz3 : IsPGroup 3 ↥(Subgroup.zpowers x) := by
      have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
      obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
    obtain ⟨P₃, hP₃⟩ := hz3.exists_le_sylow
    obtain ⟨⟨hHeis, -⟩, -⟩ :=
      CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 _ ⟨ψ'⟩ P₃ _ rfl _ rfl
    have h1 := Monoid.pow_exponent_eq_one
      (⟨x, hP₃ (Subgroup.mem_zpowers x)⟩ : ↥(P₃ : Subgroup (↥Q ⧸ Subgroup.center ↥Q)))
    rw [hHeis.2.2] at h1
    exact congrArg Subtype.val h1
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hperm := perm_D e hinn h hcen
  rw [hx] at hperm
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ pImg Q e (S ⊓ Q), t * x * t⁻¹ = x⁻¹ := by
    by_cases hx1 : x = 1
    · exact ⟨1, Subgroup.one_mem _, by simp [hx1]⟩
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    by_cases hxN : x ∉ Subgroup.normalizer (pImg Q e (S ⊓ Q) : Set (↥Q ⧸ Subgroup.center ↥Q))
    · exact exists_inv_of_perm hT2 hxo hperm hxN
    push Not at hxN
    exfalso
    have hTR : pImg Q e (S ⊓ Q) ≤
        Subgroup.normalizer (pImg Q e R : Set (↥Q ⧸ Subgroup.center ↥Q)) := by
      intro t ht
      obtain ⟨s, hsQ, hsS, rfl⟩ := (mem_pImg Q e).1 ht
      apply mem_normalizer_of_conj_mem
      intro y hy
      obtain ⟨r, hrQ, hrR, rfl⟩ := (mem_pImg Q e).1 hy
      have hsr : s * r * s⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (h.S_le_R (Subgroup.mem_inf.mp hsS).1) r).mp hrR
      refine (mem_pImg Q e).2 ⟨s * r * s⁻¹, Q.mul_mem (Q.mul_mem hsQ hrQ) (Q.inv_mem hsQ), hsr, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have h5 : 5 ∣ Nat.card (pImg Q e R) := by
      have hinj : Function.Injective (toP Q e) :=
        (MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_toP, hZ])
      rw [pImg, Subgroup.card_map_of_injective hinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R_le).toEquiv]
      obtain ⟨e₄⟩ := exists_l24_of_lieModel h.R_type
      have hdvd : Nat.card (ModO2 R) ∣ Nat.card R := Subgroup.card_quotient_dvd_card _
      rw [Nat.card_congr e₄.toEquiv, CFSG.Timmesfeld.RankOne.card_psl2_four] at hdvd
      exact (show 5 ∣ 60 by norm_num).trans hdvd
    have hxR := @mem_normalizer_of_lattice ↥CFSG.Sporadic.J2.J (↥Q ⧸ Subgroup.center ↥Q)
      (Subgroup.toGroup _) _ _ _ ψ j2Ctx.S CFSG.Quasithin.S146zY.j2_S_sylow j2Ctx.S_card
      j2Ctx.Y (fun Z hZ => j2_overgroup hZ) (j2_not_normal hnn) (j2_Y1_le_Y3 hincl)
      CFSG.Sporadic.J2.card_J _ hT2 hTi _ hxo hperm hxN _ hTR h5
    exact not_le_normalizer_of_not e hinn h hnot (by rw [hx]; exact Subgroup.zpowers_le.mpr hxR)
  obtain ⟨t₀, ht₀Q, ht₀S, rfl⟩ := (mem_pImg Q e).1 ht
  exact ⟨pow_three_mem_centralizer e hinn h hQperf hx hx3,
    t₀, ht₀S, conj_mul_mem_centralizer e hinn h hQperf hx ht₀Q htx⟩

end CFSG.Quasithin.H13.NQCat.T3
