module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin.S152O4

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem gam_commute_trivial : ∀ m : Vec, detQ m = 1 → ∀ γ s : Gam, γ ≠ 1 → γ ^ 3 = 1 →
    act γ m = m → s ^ 2 = 1 → s * γ = γ * s → s = 1 := by decide +kernel

theorem gam_sq_of_two_pow {s : Gam} {k : ℕ} (hs : s ^ (2 ^ k) = 1) : s ^ 2 = 1 := by
  have h6 : orderOf s ∣ 6 := orderOf_dvd_of_pow_eq_one (pow_six s)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hs)
  have hm2 : m < 2 := by
    by_contra hcon
    have h4 : 4 ∣ 2 ^ m := by
      have : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
      simpa using this
    rw [← hm] at h4
    exact absurd (h4.trans h6) (by norm_num)
  have : orderOf s ∣ 2 := by
    rw [hm]
    interval_cases m <;> simp
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem Bw_relIndex_of_ctx (h : Ctx T M g A t d x) :
    (qOf T).relIndex (Bw T d x) ≤ 2 := by
  classical
  have hzZ := sq_mem_omegaOneCenter h.c h.hD h.hd4
  have hdd := dd_facts h.hd4
  have hu₀U := u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ
  have hu₀z := u0Of_sq h.c h.hD h.hd4 h.hx h.hx3
  have hNd := oTwoUpper_le_centralizer_d h.c h.hD h.hd4
  set u₀ := u0Of d x with hu₀def
  have h2 : IsPGroup 2 ↥(Bw T d x) := Bw_pGroup_of_ctx h
  have hBH : Bw T d x ≤ mcOf T := inf_le_left.trans inf_le_left
  obtain ⟨-, ω, hωC, hωord⟩ := h.c.card_centralizer_oTwoUpper hzZ hdd.2 hu₀U hu₀z
  have hωN : ω ∈ oTwoUpper (mcOf T) := hωC.1
  have hωH : ω ∈ mcOf T := oTwoUpper_le _ hωN
  have hωu : ω * u₀ = u₀ * ω := Subgroup.mem_centralizer_singleton_iff.mp hωC.2
  have hωK : ω ∈ K0 T d x := by
    refine ⟨hωN, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hωd : ω * d = d * ω := Subgroup.mem_centralizer_singleton_iff.mp (hNd hωN)
    rw [wOfX_eq_mul_u0Of]
    calc ω * (d * u₀) = (ω * d) * u₀ := by rw [mul_assoc]
      _ = (d * ω) * u₀ := by rw [hωd]
      _ = d * (u₀ * ω) := by rw [mul_assoc, hωu]
      _ = (d * u₀) * ω := by rw [mul_assoc]
  obtain ⟨cm, ρ, hρinj, hρcm, hdet, hM1, -, hρrel⟩ := exists_gam_model_idx h.c
  have hρrel' : ρ.range.relIndex h.c.actK.range = 2 := hρrel
  let f : ↥(Bw T d x) →* MulAut (UT T M) := h.c.actK.comp (Subgroup.inclusion hBH)
  have hfapply : ∀ b : ↥(Bw T d x), f b = h.c.actK ⟨b, hBH b.2⟩ := fun b => rfl
  have hker : f.ker = (qOf T).subgroupOf (Bw T d x) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hfapply]
    exact ⟨fun h1 => h.c.mem_qOf_of_actK_eq_one h1, fun h1 => h.c.actK_eq_one_of_mem_qOf h1⟩
  have hrelidx : (qOf T).relIndex (Bw T d x) = Nat.card f.range := by
    show ((qOf T).subgroupOf (Bw T d x)).index = _
    rw [← hker, Subgroup.index_ker]
  obtain ⟨γ, hγ3, hγ⟩ := hM1 ω hωH hωN
  have hωpow : ω ^ 3 = 1 := by rw [← hωord]; exact pow_orderOf_eq_one ω
  have hγ1 : γ ≠ 1 := by
    intro h1
    have hQ : ω ∈ qOf T := h.c.mem_qOf_of_actK_eq_one (x := ⟨ω, hωH⟩) (by rw [hγ, h1, map_one])
    have hQ2 : IsPGroup 2 ↥(qOf T) := h.c.hyp.sylow.1.to_le (qOf_le_T_of_hyp h.c.h1281)
    obtain ⟨j, hj⟩ := hQ2 ⟨ω, hQ⟩
    have hω1 : ω ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    have hω : ω = 1 := by
      have h5 := pow_gcd_eq_one.mpr ⟨hω1, hωpow⟩
      have hg : Nat.gcd (2 ^ j) 3 = 1 := Nat.Coprime.pow_left j (by norm_num)
      rwa [hg, pow_one] at h5
    rw [hω, orderOf_one] at hωord
    omega
  have hu₀nc : u₀ * u₀ ≠ 1 := by rw [hu₀z]; exact hdd.2
  have hdet1 : detQ (cm (tclsE h.c.hUN hu₀U)) = 1 := by
    apply zmod_two_ne_zero
    intro h0
    exact hu₀nc ((hdet u₀ hu₀U).mp h0)
  have hfix : h.c.actK ⟨ω, hωH⟩ (tclsE h.c.hUN hu₀U) = tclsE h.c.hUN hu₀U := by
    have hnc : ω * u₀ * ω⁻¹ = u₀ := by rw [hωu]; group
    have hu' : ω * u₀ * ω⁻¹ ∈ uOfL22 T M := by rw [hnc]; exact hu₀U
    show actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) (hHN_of T) h.c.hHU
      ⟨ω, hωH⟩ (tclsE h.c.hUN hu₀U) = _
    rw [actTilde_tclsE h.c.hUN (hHN_of T) h.c.hHU ⟨ω, hωH⟩ hu₀U hu']
    exact tclsE_congr h.c.hUN hu' hu₀U hnc
  have hγfix : act γ (cm (tclsE h.c.hUN hu₀U)) = cm (tclsE h.c.hUN hu₀U) := by
    rw [← hρcm, ← hγ, hfix]
  have hbot : ρ.range ⊓ f.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro e ⟨⟨s, hs⟩, ⟨b, hb⟩⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 b
    have hbk : b ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one b
    have hsk : s ^ (2 ^ k) = 1 := by
      apply hρinj
      rw [map_pow, hs, map_one, ← hb, ← map_pow, hbk, map_one]
    have hs2 := gam_sq_of_two_pow hsk
    have hcomm : s * γ = γ * s := by
      apply hρinj
      rw [map_mul, map_mul, hs, ← hγ, ← hb]
      have hbω : (⟨b, hBH b.2⟩ : ↥(mcOf T)) * ⟨ω, hωH⟩ = ⟨ω, hωH⟩ * ⟨b, hBH b.2⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 ω hωK).symm
      rw [hfapply, ← map_mul, ← map_mul, hbω]
    rw [← hs, gam_commute_trivial _ hdet1 γ s hγ1 hγ3 hγfix hs2 hcomm, map_one]
  have hfrange : f.range ≤ h.c.actK.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBH b.2⟩, rfl⟩
  have hfin : ρ.range.relIndex f.range = Nat.card f.range := by
    rw [← Subgroup.inf_relIndex_right, hbot, Subgroup.relIndex_bot_left]
  have hle : ρ.range.relIndex f.range ≤ ρ.range.relIndex h.c.actK.range :=
    Subgroup.relIndex_le_of_le_right hfrange (by rw [hρrel']; norm_num)
  rw [hrelidx, ← hfin]
  rw [hρrel'] at hle
  exact hle

end InspW2

end S143

end CFSG.Quasithin
