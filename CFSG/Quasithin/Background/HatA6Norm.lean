module

public import CFSG.Quasithin.Background.HatA6NormKer
import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Orbit

public section

namespace CFSG.Quasithin.HatA6

open CFSG.Quasithin.H13.Orbit

variable {W : Type} [CommGroup W] [Finite W] {K : Subgroup (MulAut W)} {z : ↥K} {f : W}

private lemma z_ne_one (S : Setup W K z f) : (z : MulAut W) ≠ 1 := by
  intro h
  have hsub : Subsingleton W := by
    refine ⟨fun a b => ?_⟩
    rw [S.fpf a (by rw [h]; rfl), S.fpf b (by rw [h]; rfl)]
  have hW1 : Nat.card W = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  rw [S.card] at hW1
  norm_num at hW1

private lemma conj_z_eq_z_or_inv (S : Setup W K z f) {n : MulAut W}
    (hn : n ∈ Subgroup.normalizer (K : Set (MulAut W))) :
    n * (z : MulAut W) * n⁻¹ = (z : MulAut W) ∨
      n * (z : MulAut W) * n⁻¹ = (z : MulAut W)⁻¹ := by
  have hzK : (z : MulAut W) ∈ K := z.2
  have hnzK : n * (z : MulAut W) * n⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hn (z : MulAut W)).mp hzK
  have hz_ne_one := z_ne_one S
  have hcenter : (⟨n * (z : MulAut W) * n⁻¹, hnzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    change (k : MulAut W) * (n * (z : MulAut W) * n⁻¹) =
      (n * (z : MulAut W) * n⁻¹) * (k : MulAut W)
    have hk' : n⁻¹ * (k : MulAut W) * n ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) k).mp k.2
    have hcomm := S.commute_z hk'
    calc
      (k : MulAut W) * (n * (z : MulAut W) * n⁻¹)
          = n * ((n⁻¹ * (k : MulAut W) * n) * (z : MulAut W)) * n⁻¹ := by group
      _ = n * ((z : MulAut W) * (n⁻¹ * (k : MulAut W) * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * (z : MulAut W) * n⁻¹) * (k : MulAut W) := by group
  rw [S.center_eq] at hcenter
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcenter
  have hzpow : (z : MulAut W) ^ m = n * (z : MulAut W) * n⁻¹ := by
    have := congrArg Subtype.val hm
    simpa using this
  have hzpow_ne_one : (z : MulAut W) ^ m ≠ 1 := by
    intro h
    have hconj_one : n * (z : MulAut W) * n⁻¹ = 1 := by
      rw [← hzpow, h]
    have hz_one : (z : MulAut W) = 1 := by
      calc
        (z : MulAut W) = n⁻¹ * (n * (z : MulAut W) * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [hconj_one]
        _ = 1 := by group
    exact hz_ne_one hz_one
  have h3 : (z : MulAut W) ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact S.pow_three
  rw [zpow_eq_zpow_emod m h3] at hzpow
  have hm_mod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
    have h1 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
    have h2 : m % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  rcases hm_mod with h | h | h
  · have hzpow0 : (z : MulAut W) ^ m = 1 := by
      rw [zpow_eq_zpow_emod m h3, h]
      simp
    exact absurd hzpow0 hzpow_ne_one
  · left
    rw [h] at hzpow
    simpa using hzpow.symm
  · right
    have hz2_inv : (z : MulAut W) ^ 2 = (z : MulAut W)⁻¹ :=
      eq_inv_of_mul_eq_one_right (show (z : MulAut W) ^ 2 * (z : MulAut W) = 1 by
        rw [← pow_succ, S.pow_three])
    rw [h] at hzpow
    have hzpow' : n * (z : MulAut W) * n⁻¹ = (z : MulAut W)⁻¹ := by
      rw [← hzpow]
      exact hz2_inv
    exact hzpow'

private lemma K_eq_semiStab_inf_centralizer (S : Setup W K z f) :
    K = semiStab (z : MulAut W) (orbitIn K f) ⊓
      Subgroup.centralizer ({(z : MulAut W)} : Set (MulAut W)) := by
  obtain ⟨v, hb, hO⟩ := S.exists_frame
  apply Subgroup.eq_of_le_of_card_ge
  · refine le_inf S.le_semiStab ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    exact (S.commute_z hk).symm
  · calc
      Nat.card ↥(semiStab (z : MulAut W) (orbitIn K f) ⊓
          Subgroup.centralizer ({(z : MulAut W)} : Set (MulAut W))) ≤ 1080 :=
        S.card_semiStab_inf_centralizer_le hb hO
      _ = Nat.card ↥K := by
        symm
        exact (quasisimple_card S.perf S.card_center (Classical.choice S.quot)).2

private lemma semiStab_le_normalizer (S : Setup W K z f) :
    semiStab (z : MulAut W) (orbitIn K f) ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
  have hKG := K_eq_semiStab_inf_centralizer S
  have hforward : ∀ t ∈ semiStab (z : MulAut W) (orbitIn K f), ∀ x ∈ K,
      t * x * t⁻¹ ∈ K := by
    intro t ht x hx
    have hmem : t * x * t⁻¹ ∈ semiStab (z : MulAut W) (orbitIn K f) ⊓
        Subgroup.centralizer ({(z : MulAut W)} : Set (MulAut W)) := by
      refine ⟨?_, ?_⟩
      · exact mul_mem (mul_mem ht (S.le_semiStab hx)) (Subgroup.inv_mem _ ht)
      · change t * x * t⁻¹ ∈ Subgroup.centralizer ({(z : MulAut W)} : Set (MulAut W))
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        simp only [Set.mem_singleton_iff] at ha
        subst ha
        have hz' : t⁻¹ * (z : MulAut W) * t = (z : MulAut W) ∨
            t⁻¹ * (z : MulAut W) * t = (z : MulAut W)⁻¹ := by
          have := mem_semiStab_iff.mp (Subgroup.inv_mem _ ht)
          simpa using this.1
        have hx_comm_z : Commute (x : MulAut W) (z : MulAut W) := S.commute_z hx
        have hx_comm : (x : MulAut W) * (t⁻¹ * (z : MulAut W) * t) =
            (t⁻¹ * (z : MulAut W) * t) * (x : MulAut W) := by
          rcases hz' with h | h
          · rw [h]
            exact hx_comm_z.eq
          · rw [h]
            exact hx_comm_z.inv_right.eq
        have hcomm : (t * x * t⁻¹) * (z : MulAut W) =
            (z : MulAut W) * (t * x * t⁻¹) := by
          calc
            (t * x * t⁻¹) * (z : MulAut W)
                = t * ((x : MulAut W) * (t⁻¹ * (z : MulAut W) * t)) * t⁻¹ := by group
            _ = t * ((t⁻¹ * (z : MulAut W) * t) * (x : MulAut W)) * t⁻¹ := by rw [hx_comm]
            _ = (z : MulAut W) * (t * x * t⁻¹) := by group
        exact hcomm.symm
    rw [← hKG] at hmem
    exact hmem
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward s hs x
  · intro hx
    have := hforward s⁻¹ (Subgroup.inv_mem _ hs) (s * x * s⁻¹) hx
    simpa [mul_assoc] using this

private lemma normalizer_le_semiStab (S : Setup W K z f) :
    Subgroup.normalizer (K : Set (MulAut W)) ≤ semiStab (z : MulAut W) (orbitIn K f) := by
  intro n hn
  rw [mem_semiStab_iff]
  constructor
  · exact conj_z_eq_z_or_inv S hn
  · have hcard : Nat.card (orbitIn K (n f)) = 18 := by
      rw [CFSG.Quasithin.H13.Lem16.card_orbitIn_apply hn f, Nat.card_coe_set_eq]
      exact S.card_orbit
    have hnf_mem : n f ∈ orbitIn K f := by
      by_contra h
      have hnf_ne_one : n f ≠ 1 := by
        intro h1
        exact S.ne_one (n.injective (by rw [h1, map_one]))
      have h45 := (S.orbit (n f) hnf_ne_one).2 h
      rw [hcard] at h45
      omega
    have hnf_orbit : n f ∈ MulAction.orbit ↥K f := by
      rwa [← orbitIn_eq_orbit]
    have horbit_eq : orbitIn K (n f) = orbitIn K f := by
      rw [orbitIn_eq_orbit, orbitIn_eq_orbit]
      exact MulAction.orbit_eq_iff.2 hnf_orbit
    have himg : n '' orbitIn K f = orbitIn K f := by
      rw [← CFSG.Quasithin.H13.Lem16.orbitIn_apply_eq hn f, horbit_eq]
    exact himg

theorem Setup.normalizer_eq_semiStab (S : Setup W K z f) :
    Subgroup.normalizer (K : Set (MulAut W)) = semiStab (z : MulAut W) (orbitIn K f) := by
  exact le_antisymm (normalizer_le_semiStab S) (semiStab_le_normalizer S)

theorem exists_normalizer_hom_perm (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 2 ^ 6)
    (hperf : Group.IsPerfect ↥K) (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6)) :
    ∃ φ : ↥(Subgroup.normalizer (K : Set (MulAut W))) →* Equiv.Perm (Fin 6),
      Function.Surjective φ ∧
        φ.ker = ((Subgroup.center ↥K).map K.subtype).subgroupOf
          (Subgroup.normalizer (K : Set (MulAut W))) := by
  obtain ⟨z, f, S⟩ := exists_setup hW2 hW hperf hZ e
  obtain ⟨v, hb, hO⟩ := S.exists_frame
  have hN := S.normalizer_eq_semiStab
  let e6 : ↥(points (z : MulAut W) (orbitIn K f)) ≃ Fin 6 :=
    (Finite.equivFin _).trans (finCongr S.card_points)
  let ψ : ↥(semiStab (z : MulAut W) (orbitIn K f)) →*
      Equiv.Perm ↥(points (z : MulAut W) (orbitIn K f)) := pointPerm S.pow_three
  let φ : ↥(Subgroup.normalizer (K : Set (MulAut W))) →* Equiv.Perm (Fin 6) :=
    (Equiv.permCongrHom e6).toMonoidHom.comp
      (ψ.comp (MulEquiv.subgroupCongr hN).toMonoidHom)
  have hz_mem : (z : MulAut W) ∈ semiStab (z : MulAut W) (orbitIn K f) := by
    refine mem_semiStab_self S.pow_three ?_
    intro w hw
    exact S.z_mem_orbit hw
  have hzle : Subgroup.zpowers (z : MulAut W) ≤ semiStab (z : MulAut W) (orbitIn K f) :=
    Subgroup.zpowers_le.mpr hz_mem
  have hker_ψ : ψ.ker = (Subgroup.zpowers (z : MulAut W)).subgroupOf
      (semiStab (z : MulAut W) (orbitIn K f)) := by
    apply le_antisymm
    · intro s hs
      rw [Subgroup.mem_subgroupOf]
      exact S.mem_zpowers_of_pointPerm_eq_one hb hO s (MonoidHom.mem_ker.mp hs)
    · intro s hs
      exact zpowers_le_ker_pointPerm S.pow_three hs
  have hker_card : Nat.card ↥ψ.ker = 3 := by
    rw [hker_ψ]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime S.pow_three (z_ne_one S)]
  have hK_card : Nat.card ↥K = 1080 :=
    (quasisimple_card S.perf S.card_center (Classical.choice S.quot)).2
  have hfrob_mem : frobAt hb ∈ semiStab (z : MulAut W) (orbitIn K f) :=
    S.frobAt_mem_semiStab hb hO
  have hfrob_not_mem : frobAt hb ∉ K := by
    intro hfrobK
    have hcomm : frobAt hb * (z : MulAut W) = (z : MulAut W) * frobAt hb :=
      S.commute_z hfrobK
    have hz_eq_inv : (z : MulAut W) = (z : MulAut W)⁻¹ := by
      rw [← S.frobAt_conj hb]
      calc
        (z : MulAut W) = ((z : MulAut W) * frobAt hb) * (frobAt hb)⁻¹ := by group
        _ = (frobAt hb * (z : MulAut W)) * (frobAt hb)⁻¹ := by rw [← hcomm]
        _ = frobAt hb * (z : MulAut W) * (frobAt hb)⁻¹ := by group
    have hzz : (z : MulAut W) * (z : MulAut W) = 1 := by
      nth_rw 1 [hz_eq_inv]
      exact inv_mul_cancel _
    have hz2_ne_one : (z : MulAut W) ^ 2 ≠ 1 := by
      intro h
      have hz2_inv : (z : MulAut W) ^ 2 = (z : MulAut W)⁻¹ :=
        eq_inv_of_mul_eq_one_right (show (z : MulAut W) ^ 2 * (z : MulAut W) = 1 by
          rw [← pow_succ, S.pow_three])
      have hz_inv_one : (z : MulAut W)⁻¹ = 1 := by
        rw [← hz2_inv]
        exact h
      exact z_ne_one S (inv_eq_one.mp hz_inv_one)
    exact hz2_ne_one hzz
  have hrelIndex_ne_one :
      K.relIndex (semiStab (z : MulAut W) (orbitIn K f)) ≠ 1 := by
    intro h
    have hle : semiStab (z : MulAut W) (orbitIn K f) ≤ K := Subgroup.relIndex_eq_one.mp h
    exact hfrob_not_mem (hle hfrob_mem)
  have hrelIndex_pos : 0 < K.relIndex (semiStab (z : MulAut W) (orbitIn K f)) := by
    by_contra h
    have hzero : K.relIndex (semiStab (z : MulAut W) (orbitIn K f)) = 0 :=
      Nat.eq_zero_of_not_pos h
    have hmul := Subgroup.relIndex_mul_card K (semiStab (z : MulAut W) (orbitIn K f))
    rw [show K ⊓ semiStab (z : MulAut W) (orbitIn K f) = K from
        inf_eq_left.mpr S.le_semiStab, hzero, zero_mul] at hmul
    exact (Nat.card_pos (α := ↥(semiStab (z : MulAut W) (orbitIn K f)))).ne' hmul.symm
  have hrelIndex_ge_two :
      2 ≤ K.relIndex (semiStab (z : MulAut W) (orbitIn K f)) := by
    have h1 : 1 ≤ K.relIndex (semiStab (z : MulAut W) (orbitIn K f)) :=
      Nat.succ_le_of_lt hrelIndex_pos
    omega
  have hsemiStab_card : 2160 ≤ Nat.card ↥(semiStab (z : MulAut W) (orbitIn K f)) := by
    have hmul := Subgroup.relIndex_mul_card K (semiStab (z : MulAut W) (orbitIn K f))
    rw [show K ⊓ semiStab (z : MulAut W) (orbitIn K f) = K from
        inf_eq_left.mpr S.le_semiStab, hK_card] at hmul
    rw [← hmul]
    calc
      2160 = 2 * 1080 := by norm_num
      _ ≤ K.relIndex (semiStab (z : MulAut W) (orbitIn K f)) * 1080 :=
        Nat.mul_le_mul_right _ hrelIndex_ge_two
  have hψ_range_card : 720 ≤ Nat.card ↥ψ.range := by
    have hmul := Subgroup.card_ker_mul_card_range ψ
    rw [hker_card] at hmul
    have h := hsemiStab_card
    rw [← hmul] at h
    omega
  have hperm_card : Nat.card (Equiv.Perm ↥(points (z : MulAut W) (orbitIn K f))) = 720 := by
    rw [Nat.card_perm, S.card_points]
    norm_num
  have hψ_surj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_le_card
    rw [hperm_card]
    exact hψ_range_card
  have hφ_surj : Function.Surjective φ :=
    (Equiv.permCongrHom e6).surjective.comp
      (hψ_surj.comp (MulEquiv.subgroupCongr hN).surjective)
  have hker_φ : φ.ker = ((Subgroup.center ↥K).map K.subtype).subgroupOf
      (Subgroup.normalizer (K : Set (MulAut W))) := by
    have hcenter_map : (Subgroup.center ↥K).map K.subtype =
        Subgroup.zpowers (z : MulAut W) := by
      rw [S.center_eq, MonoidHom.map_zpowers]
      rfl
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hcenter_map]
    have hφ_apply : φ s = (Equiv.permCongrHom e6) (ψ ((MulEquiv.subgroupCongr hN) s)) :=
      rfl
    rw [hφ_apply, (Equiv.permCongrHom e6).map_eq_one_iff, ← MonoidHom.mem_ker, hker_ψ,
      Subgroup.mem_subgroupOf]
    have hcongr_apply : ((MulEquiv.subgroupCongr hN) s : MulAut W) = (s : MulAut W) := by
      rw [MulEquiv.subgroupCongr_apply]
    rw [hcongr_apply]
  exact ⟨φ, hφ_surj, hker_φ⟩

end CFSG.Quasithin.HatA6

end
