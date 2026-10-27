module

public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftTwo
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110One

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped Pointwise

namespace E2.BorelLift

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem oTwoUpper_eq_conjClosure_T {H K T : Subgroup Γ} (hK : ⁅K, K⁆ = K) (hT : IsPGroup 2 T)
    (hHK : H = K ⊔ T) : oTwoUpper H = conjClosure K T := by
  have hTH : T ≤ H := hHK ▸ le_sup_right
  rw [Vol2.Ch11.SecB.oTwoUpper_eq_conjClosure hK hT hHK]
  refine le_antisymm (conjClosure_le fun h hh k hk => ?_) (conjClosure_mono le_rfl hTH)
  have hN : H ≤ Subgroup.normalizer (conjClosure K T : Set Γ) := by
    rw [hHK]
    exact sup_le (fun k hk => Subgroup.le_normalizer (le_conjClosure K T hk))
      (le_normalizer_conjClosure K T)
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) k).mp (le_conjClosure K T hk)

theorem isComponent_star_of_eq {H M L : Subgroup Γ} (hJ : kerIn M H = pCoreOf 2 H)
    (hL : L ∈ cComp H) (hq : CFSG.IsQuasisimple ↥(E2.star M H L)) :
    CFSG.IsComponent (E2.star M H L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (starPi M H).ker = (pCoreOf 2 H).subgroupOf H := by
    unfold starPi
    rw [QuotientGroup.ker_mk', hJ]
  have h2 : IsPGroup 2 (starPi M H).ker := by
    rw [hker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).symm
  have : Group.IsNilpotent (starPi M H).ker := h2.isNilpotent
  have h1 := map_mem_cComp_top (starPi M H) (starPi_surjective _ _) inferInstance
    (subgroupOf_mem_cComp hL)
  exact ⟨hq, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp h1)⟩

omit [Finite Γ] in
theorem cjSub_mem_cComp {H K : Subgroup Γ} (hK : K ∈ cComp H) {u : Γ} (hu : u ∈ H) :
    cjSub u K ∈ cComp H := by
  have := cComp_map_mulEquiv (MulAut.conj u) hK
  rwa [Vol2.Ch11.SecB.map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hu)] at this

theorem isComponent_star_cjSub {H M K : Subgroup Γ} (hK : K ∈ cComp H)
    (hJ : kerIn M H = pCoreOf 2 H) (hsimple : IsSimpleGroup ↥(E2.star M H K)) {u : Γ}
    (hu : u ∈ H) : CFSG.IsComponent (E2.star M H (cjSub u K)) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hKperf : Group.IsPerfect ↥(E2.star M H K) := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
    exact Group.IsPerfect.ofSurjective (starRes_surjective (M' := M) hKH)
  have hKq : CFSG.IsQuasisimple ↥(E2.star M H K) := isQuasisimple_of_isSimpleGroup_of_isPerfect
  refine isComponent_star_of_eq hJ (cjSub_mem_cComp hK hu) ?_
  rw [star_cjSub_eq hu]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective) hKq

theorem inf_le_normalizer_one {H T M K : Subgroup Γ} (hT : IsSylowTwoOf T H) (hTM : T ≤ M)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T) (hJ : kerIn M H = pCoreOf 2 H)
    (hsimple : IsSimpleGroup ↥(E2.star M H K))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    M ⊓ K ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup Γ) : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := oTwoUpper H with hRdef
  set π := starPi M H with hπ
  set Ks := E2.star M H K with hKs
  set Rs := E2.star M H R with hRs
  set Cs := Rs ⊓ Subgroup.centralizer (Ks : Set (E2.StarQuot M H)) with hCs
  set Ss := E2.star M H T ⊓ Rs with hSs
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hReq : R = conjClosure K T := oTwoUpper_eq_conjClosure_T hperf hT.2.1 hHK
  have hKR : K ≤ R := hReq ▸ le_conjClosure K T
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow hT
  have hKperf : Group.IsPerfect ↥Ks := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
    exact Group.IsPerfect.ofSurjective (starRes_surjective (M' := M) hKH)
  have hKq : CFSG.IsQuasisimple ↥Ks := isQuasisimple_of_isSimpleGroup_of_isPerfect
  have hcomp : ∀ t ∈ T, CFSG.IsComponent (E2.star M H (cjSub t K)) := fun t ht =>
    isComponent_star_cjSub hK hJ hsimple (hT.1 ht)
  have hKc := isComponent_star_of_eq hJ hK hKq
  have hRKC : Rs = Ks ⊔ Cs := by
    refine le_antisymm ?_ (sup_le (Subgroup.map_mono fun x hx => hKR hx) inf_le_left)
    have hgen : R ≤ ((Ks ⊔ Cs).comap π).map H.subtype := by
      rw [hReq]
      refine conjClosure_le fun t ht k hk => ?_
      have htH := hT.1 ht
      have hkH := hKH hk
      refine ⟨⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹, ?_, rfl⟩
      show π (⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹) ∈ Ks ⊔ Cs
      have hgt : π (⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹) ∈ E2.star M H (cjSub t K) :=
        starPi_mem_star (by rw [mem_cjSub]; simpa [mul_assoc] using hk)
      have hgR : π (⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹) ∈ Rs := by
        refine starPi_mem_star ?_
        rw [hReq]
        simpa using mem_conjClosure ht hk
      rcases CFSG.LocalCores.distinct_components_commute hKc (hcomp t ht) with h | h
      · refine Subgroup.mem_sup_left ?_
        rw [hKs, h]
        exact hgt
      · refine Subgroup.mem_sup_right ⟨hgR, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have h1 := Subgroup.commutator_mem_commutator hx hgt
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
    obtain ⟨x', hx', hxx'⟩ := hgen hx
    rw [show x = x' from Subtype.ext hxx'.symm]
    exact hx'
  have hc : ∀ x ∈ Ks, ∀ y ∈ Cs, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have hZ : Subgroup.center ↥Ks = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Ks) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hKq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have ha : (a' : ↥Ks ⧸ Subgroup.center ↥Ks) = 1 :=
        (QuotientGroup.eq_one_iff a').mpr (h ▸ Subgroup.mem_top a')
      have hb : (b' : ↥Ks ⧸ Subgroup.center ↥Ks) = 1 :=
        (QuotientGroup.eq_one_iff b').mpr (h ▸ Subgroup.mem_top b')
      rw [ha, hb]
  have hKC : Ks ⊓ Cs = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, -, hxC⟩
    have hx : (⟨x, hxK⟩ : ↥Ks) ∈ Subgroup.center ↥Ks := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)
  have hS : IsSylowTwoOf Ss Rs := by
    have hT1 : IsSylowTwoOf (E2.star M H T) ⊤ := by
      have h1 := Setup.Family.isSylowTwoOf_map_range π hT
      rwa [MonoidHom.range_eq_top_of_surjective _ (starPi_surjective _ _)] at h1
    refine A4.isSylowTwoOf_inf_normal hT1 le_top fun y _ => ?_
    obtain ⟨h, rfl⟩ := starPi_surjective M H y
    exact starPi_mem_normalizer (le_normalizer_oTwoUpper H h.2)
  have hSK : Ss ⊓ Ks = E2.star M H (T ⊓ K) := by
    have hKsR : Ks ≤ Rs := Subgroup.map_mono fun x hx => hKR hx
    rw [hSs, inf_assoc, inf_eq_right.mpr hKsR]
    have hker : π.ker ≤ T.subgroupOf H := by
      intro x hx
      rw [MonoidHom.mem_ker, hπ, starPi_eq_one_iff, hJ] at hx
      exact Subgroup.mem_subgroupOf.mpr (hQT hx)
    have h1 := Vol2.Ch11.SecB.map_inf_eq_of_ker_le π (Q := K.subgroupOf H) hker
    rw [← Vol2.Ch11.SecB.inf_subgroupOf'] at h1
    exact h1.symm
  intro m hm
  have hmH : m ∈ H := hKH hm.2
  have hmN : π ⟨m, hmH⟩ ∈ Subgroup.normalizer ((Ss ⊓ Ks : Subgroup _) : Set (E2.StarQuot M H)) := by
    have h1 : π ⟨m, hmH⟩ ∈ E2.star M H (M ⊓ K) := starPi_mem_star hm
    rw [borel_eq hT hTM hK hB] at h1
    rw [hSK]
    exact h1.2
  have hmS := mem_normalizer_of_commute hRKC hc hKC hS (starPi_mem_star hm.2) hmN
  refine mem_normalizer_of_conj_mem' fun x hx => ⟨?_, ?_⟩
  · have hxH : x ∈ H := hT.1 hx.1
    have h1 : π ⟨x, hxH⟩ ∈ Ss := ⟨starPi_mem_star hx.1, starPi_mem_star hx.2⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp hmS _).mp h1
    rw [← map_mul, ← map_inv, ← map_mul] at h2
    obtain ⟨y, hy, hyx⟩ := mem_star510_iff.mp h2.1
    have h3 := starPi_eq_iff.mp hyx
    rw [hJ] at h3
    have h4 : (y : Γ) * ((y : Γ)⁻¹ * (m * x * m⁻¹)) ∈ T :=
      T.mul_mem hy (hQT (by simpa using h3))
    simpa using h4
  · exact R.mul_mem (R.mul_mem (hKR hm.2) hx.2) (R.inv_mem (hKR hm.2))

omit [Finite Γ] in
theorem comm_mem_of_mem_closure {N : Subgroup Γ} {X : Set Γ}
    (hXN : ∀ x ∈ X, x ∈ Subgroup.normalizer (N : Set Γ))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N) :
    ∀ a ∈ Subgroup.closure X, ∀ b ∈ Subgroup.closure X, a * b * a⁻¹ * b⁻¹ ∈ N := by
  have hcl : Subgroup.closure X ≤ Subgroup.normalizer (N : Set Γ) :=
    (Subgroup.closure_le _).mpr hXN
  have hconj : ∀ g ∈ Subgroup.closure X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (hcl hg) n).mp hn
  have hconj' : ∀ g ∈ Subgroup.closure X, ∀ n ∈ N, g⁻¹ * n * g ∈ N := fun g hg n hn => by
    have := hconj g⁻¹ ((Subgroup.closure X).inv_mem hg) n hn
    simpa using this
  have step : ∀ y ∈ X, ∀ a ∈ Subgroup.closure X, a * y * a⁻¹ * y⁻¹ ∈ N := by
    intro y hy a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hX x hx y hy
    | one => simp
    | mul a₁ a₂ ha₁ ha₂ h₁ h₂ =>
      have e : a₁ * a₂ * y * (a₁ * a₂)⁻¹ * y⁻¹ =
          (a₁ * (a₂ * y * a₂⁻¹ * y⁻¹) * a₁⁻¹) * (a₁ * y * a₁⁻¹ * y⁻¹) := by group
      rw [e]
      exact N.mul_mem (hconj a₁ ha₁ _ h₂) h₁
    | inv a ha h =>
      have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a := by group
      rw [e]
      exact hconj' a ha _ (N.inv_mem h)
  intro a ha b hb
  induction hb using Subgroup.closure_induction with
  | mem y hy => exact step y hy a ha
  | one => simp
  | mul b₁ b₂ hb₁ hb₂ h₁ h₂ =>
    have e : a * (b₁ * b₂) * a⁻¹ * (b₁ * b₂)⁻¹ =
        (a * b₁ * a⁻¹ * b₁⁻¹) * (b₁ * (a * b₂ * a⁻¹ * b₂⁻¹) * b₁⁻¹) := by group
    rw [e]
    exact N.mul_mem h₁ (hconj b₁ hb₁ _ h₂)
  | inv b hb h =>
    have e : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = b⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * b := by group
    rw [e]
    exact hconj' b hb _ (N.inv_mem h)

theorem comm_mem_of_cjSub {H T M K : Subgroup Γ} (hT : IsSylowTwoOf T H) (hTM : T ≤ M)
    (hMH : M ≤ H) (hK : K ∈ cComp H) (hJ : kerIn M H = pCoreOf 2 H)
    (hsimple : IsSimpleGroup ↥(E2.star M H K))
    (hcK : ∀ a ∈ M ⊓ K, ∀ b ∈ M ⊓ K, a * b * a⁻¹ * b⁻¹ ∈ T)
    {u u' : Γ} (hu : u ∈ T) (hu' : u' ∈ T) {x y : Γ} (hx : x ∈ M ⊓ cjSub u K)
    (hy : y ∈ M ⊓ cjSub u' K) : x * y * x⁻¹ * y⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQ
  have hQT : Q ≤ T := pCoreOf_le_of_sylow hT
  have hQN : H ≤ Subgroup.normalizer (Q : Set Γ) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hxH : x ∈ H := hMH hx.1
  have hyH : y ∈ H := hMH hy.1
  have hcu : ∀ a ∈ M ⊓ cjSub u K, ∀ b ∈ M ⊓ cjSub u K, a * b * a⁻¹ * b⁻¹ ∈ T := by
    intro a ha b hb
    have huM : u ∈ M := hTM hu
    have ha' : u⁻¹ * a * u ∈ M ⊓ K :=
      ⟨M.mul_mem (M.mul_mem (M.inv_mem huM) ha.1) huM, mem_cjSub.mp ha.2⟩
    have hb' : u⁻¹ * b * u ∈ M ⊓ K :=
      ⟨M.mul_mem (M.mul_mem (M.inv_mem huM) hb.1) huM, mem_cjSub.mp hb.2⟩
    have h1 := hcK _ ha' _ hb'
    have e : a * b * a⁻¹ * b⁻¹ =
        u * ((u⁻¹ * a * u) * (u⁻¹ * b * u) * (u⁻¹ * a * u)⁻¹ * (u⁻¹ * b * u)⁻¹) * u⁻¹ := by
      group
    rw [e]
    exact T.mul_mem (T.mul_mem hu h1) (T.inv_mem hu)
  by_cases heq : E2.star M H (cjSub u K) = E2.star M H (cjSub u' K)
  ·
    have hy' : starPi M H ⟨y, hyH⟩ ∈ E2.star M H (cjSub u K) := heq ▸ starPi_mem_star hy.2
    obtain ⟨z, hz, hzy⟩ := mem_star510_iff.mp hy'
    have hq := starPi_eq_iff.mp hzy
    rw [hJ] at hq
    set q := (z : Γ)⁻¹ * y with hqdef
    have hzM : (z : Γ) ∈ M := by
      have : (z : Γ) = y * q⁻¹ := by rw [hqdef]; group
      rw [this]
      exact M.mul_mem hy.1 (M.inv_mem (hTM (hQT hq)))
    have h1 := hcu x hx z ⟨hzM, hz⟩
    have hyz : y = z * q := by rw [hqdef]; group
    rw [hyz]
    have e : x * (z * q) * x⁻¹ * (z * q)⁻¹ =
        (x * z * x⁻¹ * (z : Γ)⁻¹) * ((z : Γ) * (x * q * x⁻¹ * q⁻¹) * (z : Γ)⁻¹) := by group
    rw [e]
    refine T.mul_mem h1 (hQT ?_)
    have hxq : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQN hxH) q).mp hq
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ Q := Q.mul_mem hxq (Q.inv_mem hq)
    exact (Subgroup.mem_normalizer_iff.mp (hQN z.2) _).mp h2
  ·
    rcases CFSG.LocalCores.distinct_components_commute
        (isComponent_star_cjSub hK hJ hsimple (hT.1 hu))
        (isComponent_star_cjSub hK hJ hsimple (hT.1 hu')) with h | h
    · exact absurd h heq
    · have h1 := Subgroup.commutator_mem_commutator (starPi_mem_star (M' := M) (H := H)
        (x := ⟨x, hxH⟩) hx.2) (starPi_mem_star (M' := M) (H := H) (x := ⟨y, hyH⟩) hy.2)
      rw [h, Subgroup.mem_bot] at h1
      have h2 : starPi M H (⟨x, hxH⟩ * ⟨y, hyH⟩ * ⟨x, hxH⟩⁻¹ * ⟨y, hyH⟩⁻¹) = 1 := by
        rw [commutatorElement_def] at h1
        simpa only [map_mul, map_inv] using h1
      have h3 := starPi_eq_one_iff.mp h2
      rw [hJ] at h3
      exact hQT (by simpa using h3)

theorem lift_one (hTor : E2.E22TorusCover)
    {H T MH K : Subgroup Γ} {n : ℕ} (hmin : MinParabolic H T MH) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hJ : kerIn MH H = pCoreOf 2 H) {t : Γ} (ht : t ∈ T)
    (hMeq : MH = MH ⊓ K ⊔ cjSub t (MH ⊓ K) ⊔ T) (hn : 2 ≤ n)
    (hty : IsPSL 2 2 n ↥(E2.star MH H K) ∨ IsSz n ↥(E2.star MH H K))
    (hB : E2.IsBorelIn (E2.star MH H K) (E2.star MH H (MH ⊓ K))) :
    E2.E22BorelLift H T MH n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T H := hmin.isSylow
  have hTM : T ≤ MH := hmin.le
  have hMH : MH ≤ H := hmin.maximal.1.le
  set Q := pCoreOf 2 H with hQ
  have hQT : Q ≤ T := pCoreOf_le_of_sylow hT
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hsimple : IsSimpleGroup ↥(E2.star MH H K) := isSimpleGroup_of_psl2_or_sz hty
  set R := oTwoUpper H with hRdef
  have hReq : R = conjClosure K T := oTwoUpper_eq_conjClosure_T hperf hT.2.1 hHK
  have hKR : K ≤ R := hReq ▸ le_conjClosure K T
  have hsK : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hT
  have hKQ : ∀ j ∈ K, j ∈ Q → j ∈ pCoreOf 2 K := fun j hjK hjQ =>
    Vol2.Ch11.SecB.inf_pCoreOf_le_pCoreOf hKH ⟨hjK, hjQ⟩
  have hP₂T : pCoreOf 2 K ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans hQT
  have hJK : ∀ j ∈ K, j ∈ kerIn MH H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K := by
    intro j hjK hjJ x hx
    rw [hJ] at hjJ
    have hj : j ∈ T ⊓ K := ⟨hP₂T (hKQ j hjK hjJ), hjK⟩
    exact (T ⊓ K).mul_mem ((T ⊓ K).mul_mem hj hx) ((T ⊓ K).inv_mem hj)
  have hBeq : MH ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) :=
    inf_eq_normalizer hT hTM hK hB hJK
  have hO : CFSG.pCore 2 ↥K ≤ (starRes MH H K hKH).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starRes_eq_one_iff]
    exact pCoreOf_le_kerIn hT hTM
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) (coe_mem_pCoreOf hk))
  have hZ : ∀ k ∈ (starRes MH H K hKH).ker, ∀ x : ↥K,
      k * x * k⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥K := by
    intro k hk x
    rw [MonoidHom.mem_ker, starRes_eq_one_iff, hJ] at hk
    have hk' : k ∈ CFSG.pCore 2 ↥K := mem_pCore_of_coe (hKQ k k.2 hk)
    have hn' : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    have := (CFSG.pCore 2 ↥K).mul_mem hk' (hn'.conj_mem k⁻¹ ((CFSG.pCore 2 ↥K).inv_mem hk') x)
    simpa [mul_assoc] using this
  have hty' : E2.IsBenderOf n ↥(E2.star MH H K) ∨ IsPSL 3 2 n ↥(E2.star MH H K) ∨
      IsPSp4 2 n ↥(E2.star MH H K) :=
    Or.inl ⟨hn, hty.elim Or.inl fun h => Or.inr (Or.inl h)⟩
  obtain ⟨hcommK, Y, w, hYle, hYc, hYcard, hwK, hwN, hwY⟩ :=
    torus_of_cover hTor (starRes MH H K hKH) (starRes_surjective hKH) hO hZ hn hty' hsK
  have hcK : ∀ a ∈ MH ⊓ K, ∀ b ∈ MH ⊓ K, a * b * a⁻¹ * b⁻¹ ∈ T := fun a ha b hb =>
    (hcommK a (hBeq ▸ ha) b (hBeq ▸ hb)).1
  have hTNR : T ≤ Subgroup.normalizer ((T ⊓ R : Subgroup Γ) : Set Γ) := by
    intro v hv
    have hvR : v ∈ Subgroup.normalizer (R : Set Γ) := le_normalizer_oTwoUpper H (hT.1 hv)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxR⟩
      exact ⟨T.mul_mem (T.mul_mem hv hxT) (T.inv_mem hv),
        (Subgroup.mem_normalizer_iff.mp hvR x).mp hxR⟩
    · rintro ⟨hxT, hxR⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hvR x).mpr hxR⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem hv) hxT) hv
      simpa [mul_assoc] using this
  have hA := inf_le_normalizer_one hT hTM hK hHK hJ hsimple hB
  have hMS : MH ≤ Subgroup.normalizer ((T ⊓ R : Subgroup Γ) : Set Γ) := by
    rw [hMeq]
    refine sup_le (sup_le hA ?_) hTNR
    rintro _ ⟨m, hm, rfl⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTNR ht) (hA hm))
      (Subgroup.inv_mem _ (hTNR ht))
    simpa [MulAut.conj_apply] using this
  have hcjR : ∀ u ∈ T, cjSub u K ≤ R := by
    intro u hu x hx
    rw [hReq]
    have hx' := mem_cjSub.mp hx
    have := mem_conjClosure hu hx'
    simpa [mul_assoc] using this
  set Xc : Set Γ := {x | ∃ u ∈ T, x ∈ MH ∧ x ∈ cjSub u K} with hXc
  set X : Set Γ := Xc ∪ ((T ⊓ R : Subgroup Γ) : Set Γ) with hX
  have hXP : X ⊆ MH ⊓ R := by
    rintro x (⟨u, hu, hxM, hxK⟩ | ⟨hxT, hxR⟩)
    · exact ⟨hxM, hcjR u hu hxK⟩
    · exact ⟨hTM hxT, hxR⟩
  set N₁ : Subgroup Γ := Subgroup.closure Xc with hN₁
  have hN₁R : N₁ ≤ R := (Subgroup.closure_le _).mpr fun x ⟨u, hu, _, hxK⟩ => hcjR u hu hxK
  have hTN₁ : T ≤ Subgroup.normalizer (N₁ : Set Γ) := by
    intro v hv
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : N₁.map (MulAut.conj v).toMonoidHom ≤ N₁ := by
      rw [hN₁, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨u, hu, hyM, hyK⟩, rfl⟩
      refine ⟨v * u, T.mul_mem hv hu, ?_, ?_⟩
      · exact MH.mul_mem (MH.mul_mem (hTM hv) hyM) (MH.inv_mem (hTM hv))
      · rw [mem_cjSub]
        have := mem_cjSub.mp hyK
        simpa [MulAut.conj_apply, mul_assoc] using this
    exact hle ⟨x, hx, rfl⟩
  have hMN₁ : MH ≤ N₁ ⊔ T := by
    have h1 : MH ⊓ K ≤ N₁ := fun x hx =>
      Subgroup.subset_closure ⟨1, T.one_mem, hx.1, by rw [mem_cjSub]; simpa using hx.2⟩
    have h2 : cjSub t (MH ⊓ K) ≤ N₁ := by
      rintro _ ⟨m, hm, rfl⟩
      refine Subgroup.subset_closure ⟨t, ht, ?_, ?_⟩
      · exact MH.mul_mem (MH.mul_mem (hTM ht) hm.1) (MH.inv_mem (hTM ht))
      · rw [mem_cjSub]
        simpa [MulAut.conj_apply, mul_assoc] using hm.2
    rw [hMeq]
    exact sup_le (sup_le (h1.trans le_sup_left) (h2.trans le_sup_left)) le_sup_right
  have hPX : MH ⊓ R ≤ Subgroup.closure X := by
    intro m hm
    have hm' : m ∈ ((N₁ ⊔ T : Subgroup Γ) : Set Γ) := hMN₁ hm.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N₁ T hTN₁] at hm'
    obtain ⟨a, ha, s, hs, rfl⟩ := hm'
    have hsR : s ∈ R := by
      have := R.mul_mem (R.inv_mem (hN₁R ha)) hm.2
      simpa using this
    have h1 : N₁ ≤ Subgroup.closure X := Subgroup.closure_mono Set.subset_union_left
    exact (Subgroup.closure X).mul_mem (h1 ha) (Subgroup.subset_closure (Or.inr ⟨hs, hsR⟩))
  have hcomm : ∀ a ∈ MH ⊓ R, ∀ b ∈ MH ⊓ R, a * b * a⁻¹ * b⁻¹ ∈ T ⊓ R := by
    have hXN : ∀ x ∈ X, x ∈ Subgroup.normalizer ((T ⊓ R : Subgroup Γ) : Set Γ) :=
      fun x hx => hMS (hXP hx).1
    have hcl := comm_mem_of_mem_closure hXN ?_
    · exact fun a ha b hb => hcl a (hPX ha) b (hPX hb)
    intro x hx y hy
    have hxR := (hXP hx).2
    have hyR := (hXP hy).2
    have hR : x * y * x⁻¹ * y⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hxR hyR) (R.inv_mem hxR)) (R.inv_mem hyR)
    rcases hy with ⟨u', hu', hy'⟩ | hyS
    · rcases hx with ⟨u, hu, hx'⟩ | hxS
      · exact ⟨comm_mem_of_cjSub hT hTM hMH hK hJ hsimple hcK hu hu' ⟨hx'.1, hx'.2⟩
          ⟨hy'.1, hy'.2⟩, hR⟩
      · have h1 : y * x⁻¹ * y⁻¹ ∈ T ⊓ R :=
          (Subgroup.mem_normalizer_iff.mp (hXN y (Or.inl ⟨u', hu', hy'⟩)) _).mp
            ((T ⊓ R).inv_mem hxS)
        have := (T ⊓ R).mul_mem hxS h1
        simpa [mul_assoc] using this
    · have h1 : x * y * x⁻¹ ∈ T ⊓ R := (Subgroup.mem_normalizer_iff.mp (hXN x hx) _).mp hyS
      exact (T ⊓ R).mul_mem h1 ((T ⊓ R).inv_mem hyS)
  refine lift_of_borel (R₀ := R) (P₂ := pCoreOf 2 K) (Y₀ := Y) (w₀ := w) hT hTM hMH
    (le_normalizer_oTwoUpper H) (oTwoUpper_le H) (hHK ▸ sup_le_sup_right hKR T) hMS hcomm
    (by omega) ((hBeq ▸ hYle).trans (inf_le_inf_left MH hKR)) hYc hYcard (hP₂T.trans hTM)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    ((hYle.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    (hKH hwK) (fun hwM => hwN ((hBeq ▸ ⟨hwM, hwK⟩ : w ∈ K ⊓ _).2)) ?_
  intro A hAY a ha
  have h1 := hwY a (hAY ha)
  have h2 : w * a * w⁻¹ = (w * a * w⁻¹ * a) * a⁻¹ := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (A.inv_mem ha))

end E2.BorelLift

end CFSG.Quasithin
