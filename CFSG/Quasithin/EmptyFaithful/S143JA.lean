module

public import CFSG.Quasithin.EmptyFaithful.S143Fuse
public import CFSG.Quasithin.EmptyFaithful.S143GC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.S143GD
public import CFSG.Quasithin.EmptyFaithful.S143ID

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Five

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.centralizer_T_yOfL22 :
    T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) = ⊥ := by
  have h := c.h1281
  have hTL : T ≤ Subgroup.normalizer (yOfL22 T M : Set G) := h.inM.2.trans h.normal
  by_contra hne
  have hNT : T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) ≤ T := inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := c.hyp.sylow.1
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  have hnorm : ((T ⊓ Subgroup.centralizer (yOfL22 T M : Set G)).subgroupOf T).Normal := by
    refine ⟨fun n hn t => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem t.2 (hNT hn)) (T.inv_mem t.2), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have hl' : (t : G)⁻¹ * l * (t : G) ∈ yOfL22 T M := by
      have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem t.2)) l).mp hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 _ hl'
    calc l * ((t : G) * (n : G) * (t : G)⁻¹)
        = (t : G) * (((t : G)⁻¹ * l * (t : G)) * (n : G)) * (t : G)⁻¹ := by group
      _ = (t : G) * ((n : G) * ((t : G)⁻¹ * l * (t : G))) * (t : G)⁻¹ := by rw [h1]
      _ = (t : G) * (n : G) * (t : G)⁻¹ * l := by group
  have hbot : (T ⊓ Subgroup.centralizer (yOfL22 T M : Set G)).subgroupOf T ≠ ⊥ := by
    intro hb
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxT : x ∈ T := hNT hx
    have : (⟨x, hxT⟩ : ↥T) ∈ (T ⊓ Subgroup.centralizer (yOfL22 T M : Set G)).subgroupOf T := hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨⟨w', hw'mem⟩, hw'ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hbot)
  have hwN : (w' : G) ∈ T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) := hw'mem.1
  have hwT : (w' : G) ∈ T := w'.2
  have hwcen : ∀ s ∈ T, s * (w' : G) = (w' : G) * s := by
    intro s hs
    have := Subgroup.mem_center_iff.mp hw'mem.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hw1 : w' ≠ 1 := fun he => hw'ne (Subtype.ext he)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) w'
  have hord : orderOf (w' : G) = 2 ^ k := by rw [Subgroup.orderOf_coe]; exact hk
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hord
    exact hw1 (Subtype.ext hord)
  have hdvd : 2 ∣ orderOf (w' : G) := by rw [hord]; exact dvd_pow_self 2 hk0
  have hw0 : orderOf (w' : G) ≠ 0 := (orderOf_pos (w' : G)).ne'
  have hw₂ord : orderOf ((w' : G) ^ (orderOf (w' : G) / 2)) = 2 := orderOf_pow_orderOf_div hw0 hdvd
  have hw₂2 : ((w' : G) ^ (orderOf (w' : G) / 2)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one ((w' : G) ^ (orderOf (w' : G) / 2))
    rwa [hw₂ord] at this
  have hw₂1 : (w' : G) ^ (orderOf (w' : G) / 2) ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hw₂ord
    exact absurd hw₂ord (by norm_num)
  have hw₂N : (w' : G) ^ (orderOf (w' : G) / 2) ∈
      T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) := Subgroup.pow_mem _ hwN _
  have hw₂Z : (w' : G) ^ (orderOf (w' : G) / 2) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw₂N).1, ?_⟩, hw₂2⟩
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    exact (Commute.pow_right (show Commute s (w' : G) from hwcen s hs) _).eq
  obtain ⟨z, a, hzZ, hz1, ha, haV, haZ, -, -, -, -, -, -⟩ := exists_three_cycle h c.goodElt
  have hw₂z : (w' : G) ^ (orderOf (w' : G) / 2) = z := by
    rcases c.mem_Z_cases hzZ hz1 hw₂Z with h1 | h1
    · exact absurd h1 hw₂1
    · exact h1
  have hzC : z ∈ Subgroup.centralizer (yOfL22 T M : Set G) := by
    rw [← hw₂z]; exact (Subgroup.mem_inf.mp hw₂N).2
  have hgz : g * z = z * g := Subgroup.mem_centralizer_iff.mp hzC g c.g_mem
  apply haZ
  have : a = z := by
    rw [ha]
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  rw [this]
  exact hzZ

theorem Counter.mem_qOf_of_centralizes_uOfL22 {x : G} (hxH : x ∈ mcOf T)
    (hx : ∀ u ∈ uOfL22 T M, u * x = x * u) : x ∈ qOf T := by
  have hcU : c.actK ⟨x, hxH⟩ = 1 := by
    refine (actTilde_eq_one_iff _ _ _ (hHN_of T) c.hHU c.hUN ⟨x, hxH⟩).mpr fun u hu => ?_
    have e : x * u * x⁻¹ * u⁻¹ = 1 := by
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [← hx u hu]
        _ = 1 := by group
    show x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T
    rw [e]; exact (quasithinOmegaOneCenter T).one_mem
  exact c.mem_qOf_of_actK_eq_one (x := ⟨x, hxH⟩) hcU

theorem Counter.centralizer_kOf_eq_bot {A : Subgroup G} {t : G} (hb : Concl18b T M A t) :
    Subgroup.centralizer (kOf T M A : Set G) = ⊥ := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  have hle := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hLK : yOfL22 T M ≤ kOf T M (c.Ac hrW hrV hr2) := le_sup_right
  have hAR : c.Ac hrW hrV hr2 ≤ rOf T M := c.Ac_le_rOf hrW hrV hr2
  rw [eq_bot_iff]
  intro x hx
  have hx' := Subgroup.mem_centralizer_iff.mp hx
  have hxA : x ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => hx' a (hle ((le_sup_left : rOf T M ≤ _) (hAR ha)))
  have hxH : x ∈ mcOf T := c.centralizer_Ac_le_mcOf hrW hrV hr2 hxA
  have hxQ : x ∈ qOf T := c.mem_qOf_of_centralizes_uOfL22 hxH fun u hu =>
    hx' u (hle ((le_sup_right : uOfL22 T M ≤ _) hu))
  have hQT : qOf T ≤ T := le_sup_right.trans (rq_le_of_hyp c.h1281)
  have hxL : x ∈ Subgroup.centralizer (yOfL22 T M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => hx' l (hLK hl)
  have : x ∈ T ⊓ Subgroup.centralizer (yOfL22 T M : Set G) := ⟨hQT hxQ, hxL⟩
  rw [c.centralizer_T_yOfL22] at this
  exact this

end Five

section Six

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

omit [Finite G] c in
theorem conj_mem_kOf_of_mem_inf {A : Subgroup G} {n x : G}
    (hnH : n ∈ mcOf T ⊓ Subgroup.normalizer (A : Set G))
    (hnL : n ∈ Subgroup.normalizer (yOfL22 T M : Set G)) (hx : x ∈ kOf T M A) :
    n * x * n⁻¹ ∈ kOf T M A := by
  have hle : kOf T M A ≤ (kOf T M A).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · show n * y * n⁻¹ ∈ kOf T M A
      exact (le_sup_left : oTwoUpper (mcOf T ⊓ Subgroup.normalizer (A : Set G)) ≤ _)
        (conj_mem_oTwoUpper (Subgroup.le_normalizer hnH) hy)
    · show n * y * n⁻¹ ∈ kOf T M A
      exact (le_sup_right : yOfL22 T M ≤ _) ((Subgroup.mem_normalizer_iff.mp hnL y).mp hy)
  exact hle hx

theorem Counter.dOf_le_normalizer_kOf {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M)
    (hr2 : r * r = 1) :
    dOf T M ≤ Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G) := by
  have hTL : T ≤ Subgroup.normalizer (yOfL22 T M : Set G) := c.h1281.inM.2.trans c.h1281.normal
  have hQT : qOf T ≤ T := le_sup_right.trans (rq_le_of_hyp c.h1281)
  have hmem : ∀ d ∈ dOf T M, d ∈ mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
    intro d hd
    have hdQ : d ∈ qOf T := (Subgroup.mem_inf.mp hd).1
    exact ⟨pCoreOf_le 2 (mcOf T) hdQ, c.normal_Ac hrW hrV hr2 (Subgroup.mem_sup_right hdQ)⟩
  intro d hd
  have hdL : d ∈ Subgroup.normalizer (yOfL22 T M : Set G) :=
    hTL (hQT (Subgroup.mem_inf.mp hd).1)
  have hd' : d⁻¹ ∈ dOf T M := (dOf T M).inv_mem hd
  exact mem_normalizer_of_conj_mem (fun x hx => conj_mem_kOf_of_mem_inf (hmem d hd) hdL hx)
    (fun x hx => by
      have := conj_mem_kOf_of_mem_inf (hmem d⁻¹ hd') ((Subgroup.normalizer _).inv_mem hdL) hx
      simpa using this)

theorem Counter.normalizer_kOf_eq {A : Subgroup G} {t : G} (hb : Concl18b T M A t)
    (hq : Concl19a T M) (hK : IsA6Block (kOf T M A) A) :
    Subgroup.normalizer (kOf T M A : Set G) = kOf T M A ⊔ dOf T M := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  have hle := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hRK : rOf T M ≤ kOf T M (c.Ac hrW hrV hr2) := le_sup_left.trans hle
  have hUK : uOfL22 T M ≤ kOf T M (c.Ac hrW hrV hr2) := le_sup_right.trans hle
  have hAK : c.Ac hrW hrV hr2 ≤ kOf T M (c.Ac hrW hrV hr2) := hK.le
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hRQT : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  have hNA : ∀ n ∈ Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G),
      n ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
    intro n hn
    have := normalizer_le_normalizer_pCoreOf 2 (kOf T M (c.Ac hrW hrV hr2)) hn
    rwa [← hK.2.1] at this
  apply le_antisymm
  · intro n hn
    have hnA := hNA n hn
    obtain ⟨z, hzZ, hz1, -⟩ := c.h1281.exists_zgen
    have hzA : z ∈ c.Ac hrW hrV hr2 :=
      c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ)
    have hnzA : n * z * n⁻¹ ∈ c.Ac hrW hrV hr2 := (Subgroup.mem_normalizer_iff.mp hnA z).mp hzA
    have hnz1 : n * z * n⁻¹ ≠ 1 := by
      intro he
      apply hz1
      have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
      rw [this, he]; group
    obtain ⟨k, hkK, hk⟩ := hK.exists_conj_of_ne_one hnzA hzA hnz1 hz1
    have hmN : k * n ∈ Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer hkK) hn
    have hmH : k * n ∈ mcOf T := by
      apply c.mem_mcOf_of_comm hzZ hz1
      calc k * n * z = (k * (n * z * n⁻¹) * k⁻¹) * (k * n) := by group
        _ = z * (k * n) := by rw [hk]
    have hmNH : k * n ∈ mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      ⟨hmH, hNA _ hmN⟩
    have hsyl := c.isSylowTwoOf_rq_inf_normalizer_Ac hrW hrV hr2
    have hNH : oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) ⊔
        (rOf T M ⊔ qOf T) = mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := by
      have := sup_twoResidual_eq hsyl
      rw [F6.twoResidual_eq_oTwoUpper, sup_comm] at this
      exact this
    have hRQN : rOf T M ⊔ qOf T ≤ Subgroup.normalizer
        (oTwoUpper (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) : Set G) := fun x hx =>
      normalizer_le_normalizer_oTwoUpper _ (Subgroup.le_normalizer (hsyl.le hx))
    rw [← hNH] at hmNH
    obtain ⟨ω, hω, ρ, hρ, hωρ⟩ :=
      (CFSG.QuasithinUnique.Lin2.mem_sup_iff_of_le_normalizer hRQN).1 hmNH
    have hQR : qOf T ≤ Subgroup.normalizer (rOf T M : Set G) := fun x hx =>
      c.T_le_normalizer_rOf' (hRQT ((le_sup_right : qOf T ≤ rOf T M ⊔ qOf T) hx))
    obtain ⟨r', hr', q, hqQ, hρrq⟩ :=
      (CFSG.QuasithinUnique.Lin2.mem_sup_iff_of_le_normalizer hQR).1 hρ
    have hDN : dOf T M ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2
    rw [hq.q_eq] at hqQ
    obtain ⟨u, hu, d, hd, hqud⟩ := (CFSG.QuasithinUnique.Lin2.mem_sup_iff_of_le_normalizer hDN).1 hqQ
    have hωK : ω ∈ kOf T M (c.Ac hrW hrV hr2) := (le_sup_left : oTwoUpper _ ≤ _) hω
    have hn_eq : n = (k⁻¹ * (ω * r' * u)) * d := by
      have h1 : k * n = ω * (r' * (u * d)) := by rw [hωρ, hρrq, hqud]
      calc n = k⁻¹ * (k * n) := by group
        _ = k⁻¹ * (ω * (r' * (u * d))) := by rw [h1]
        _ = (k⁻¹ * (ω * r' * u)) * d := by group
    rw [hn_eq]
    refine Subgroup.mul_mem_sup (Subgroup.mul_mem _ ((kOf T M _).inv_mem hkK)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hωK (hRK hr')) (hUK hu))) hd
  · exact sup_le Subgroup.le_normalizer (c.dOf_le_normalizer_kOf hrW hrV hr2)

end Six

end S143

end CFSG.Quasithin
