module

public import CFSG.Quasithin.EmptyFaithful.S143GB
public import CFSG.Quasithin.EmptyFaithful.S143FK
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Centralizer

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.eq_one_of_mem_centralizer_Ac {x : G}
    (hx : x ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) (hodd : Odd (orderOf x)) :
    x = 1 := by
  have hUN := c.hUN
  have hHN := hHN_of T
  have hZA : quasithinOmegaOneCenter T ≤ c.Ac hrW hrV hr2 := fun z hz =>
    c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hz)
  have hxH : x ∈ mcOf T := Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Subgroup.mem_centralizer_iff.mp hx z (hZA hz)
  have hxN : x ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    Subgroup.centralizer_le_normalizer _ hx
  have hαT := c.alphaOf_mem_T hrW hrV hr2
  have hα1 := c.alphaOf_ne_one hrW hrV hr2
  have hαx := c.alphaOf_tclsE hrW hrV hr2
  have hcomm := (c.mem_normalizer_Ac_iff hrW hrV hr2 ⟨x, hxH⟩).mp hxN
  obtain ⟨b, hbB, hbZ⟩ : ∃ b ∈ c.Ac hrW hrV hr2 ⊓ qOf T, b ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card ↥(c.Ac hrW hrV hr2 ⊓ qOf T) ≤ Nat.card ↥(quasithinOmegaOneCenter T) :=
      Subgroup.card_le_of_le fun b hb => hall b hb
    rw [c.card_inf_qOf_Ac hrW hrV hr2, c.h1281.card_omegaOneCenter] at h1
    omega
  have hbU : b ∈ uOfL22 T M := c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2 hbB
  have hw : tclsE hUN hbU ≠ 1 := fun he => hbZ ((tclsE_eq_one_iff hUN hbU).mp he)
  have hxb : x * b * x⁻¹ = b := by
    have h1 : b * x = x * b := Subgroup.mem_centralizer_iff.mp hx b hbB.1
    calc x * b * x⁻¹ = (b * x) * x⁻¹ := by rw [h1]
      _ = b := by group
  have hxbU : x * b * x⁻¹ ∈ uOfL22 T M := by rw [hxb]; exact hbU
  have hyw : c.actK ⟨x, hxH⟩ (tclsE hUN hbU) = tclsE hUN hbU := by
    have := actTilde_tclsE hUN hHN c.hHU ⟨x, hxH⟩ hbU hxbU
    exact this.trans (tclsE_congr hUN hxbU hbU hxb)
  have hy : c.actK ⟨x, hxH⟩ ∈
      Subgroup.centralizer ({c.alphaOf hrW hrV hr2} : Set (MulAut (UT T M))) ⊓ c.actK.range :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm, ⟨⟨x, hxH⟩, rfl⟩⟩
  have hxodd' : Odd (orderOf (⟨x, hxH⟩ : ↥(mcOf T))) := by
    rw [Subgroup.orderOf_mk]; exact hodd
  have hodd' : Odd (orderOf (c.actK ⟨x, hxH⟩)) :=
    Odd.of_dvd_nat hxodd' (orderOf_map_dvd _ _)
  have h1 := c.odd_fix_trivial hrW hrV hr2 hαT hα1 hαx hy hodd' hw hyw
  have hxQ : x ∈ qOf T := c.mem_qOf_of_actK_eq_one (x := ⟨x, hxH⟩) h1
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨x, hxQ⟩
  have hxk : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have : orderOf x = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.mp this

theorem Counter.isPGroup_centralizer_Ac :
    IsPGroup 2 (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have h1 : (x ^ (2 ^ a)) ^ m = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hy : x ^ (2 ^ a) ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).pow_mem hx _
  have hodd : Odd (orderOf (x ^ (2 ^ a))) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  have := c.eq_one_of_mem_centralizer_Ac hrW hrV hr2 hy hodd
  exact ⟨a, Subtype.ext (by simpa using this)⟩

theorem Counter.centralizer_Ac_le_mcOf :
    Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ≤ mcOf T := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun z hz => Subgroup.mem_centralizer_iff.mp hx z
    (c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hz))

theorem Counter.inf_centralizer_rq_le :
    c.Ac hrW hrV hr2 ⊓ Subgroup.centralizer ((rOf T M ⊔ qOf T : Subgroup G) : Set G) ≤
      quasithinOmegaOneCenter T := by
  rintro a ⟨haA, haC⟩
  have haH := c.Ac_le_mcOf hrW hrV hr2 haA
  have hUQ : uOfL22 T M ≤ rOf T M ⊔ qOf T := (uOfL22_le_qOf c).trans le_sup_right
  have hcU : c.actK ⟨a, haH⟩ = 1 := by
    refine (actTilde_eq_one_iff _ _ _ (hHN_of T) c.hHU c.hUN ⟨a, haH⟩).mpr fun u hu => ?_
    have h1 : u * a = a * u := Subgroup.mem_centralizer_iff.mp haC u (hUQ hu)
    have e : a * u * a⁻¹ * u⁻¹ = 1 := by
      calc a * u * a⁻¹ * u⁻¹ = (u * a) * a⁻¹ * u⁻¹ := by rw [← h1]
        _ = 1 := by group
    show a * u * a⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T
    rw [e]; exact (quasithinOmegaOneCenter T).one_mem
  have haQ : a ∈ qOf T := c.mem_qOf_of_actK_eq_one (x := ⟨a, haH⟩) hcU
  have haU : a ∈ uOfL22 T M := c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2 ⟨haA, haQ⟩
  have hcen : a ∈ centerOf (uOfL22 T M) :=
    ⟨haU, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp haC u (hUQ hu)⟩
  rwa [c.centerOf_uOfL22_eq] at hcen

theorem Counter.card_inf_normalizer_Ac :
    Nat.card ↥(mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) =
      12 * Nat.card ↥(qOf T) := by
  obtain ⟨e⟩ := c.nh_iso hrW hrV hr2
  have hXH : mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) ≤ mcOf T := inf_le_left
  have h1 := card_imageOTwoQuot_mul hXH
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T)
      (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))) = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have h1' : Nat.card (Multiplicative (ZMod 2)) = 2 := by rw [Nat.card_eq_fintype_card]; rfl
    have h2' : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
    rw [h1', h2']
  have hQN : qOf T ≤ mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    le_inf (pCoreOf_le 2 (mcOf T)) ((le_sup_right.trans (c.normal_Ac hrW hrV hr2)))
  have hQ : (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) ⊓ pCoreOf 2 (mcOf T) =
      qOf T := inf_eq_right.mpr hQN
  rw [hcard, hQ] at h1
  exact h1.symm

theorem Counter.isSylowTwoOf_rq_inf_normalizer_Ac :
    IsSylowTwoOf (rOf T M ⊔ qOf T)
      (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) := by
  have hRQN : rOf T M ⊔ qOf T ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (sup_le_sup_right (pCoreOf_le 2 (iTwo T M)) _).trans (c.normal_Ac hrW hrV hr2)
  have hRQH : rOf T M ⊔ qOf T ≤ mcOf T :=
    sup_le (rOf_le_mcOf c) (pCoreOf_le 2 (mcOf T))
  have hle : rOf T M ⊔ qOf T ≤ mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    le_inf hRQH hRQN
  have hP2 : IsPGroup 2 ↥(rOf T M ⊔ qOf T) := c.hyp.sylow.1.to_le (rq_le_of_hyp c.h1281)
  refine ⟨hle, hP2, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (rOf T M ⊔ qOf T)
    (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
  rw [inf_eq_left.mpr hle, c.card_inf_normalizer_Ac hrW hrV hr2, card_rOf_sup_qOf c] at h1
  have hpos : 0 < Nat.card ↥(qOf T) := Nat.card_pos
  have h2 : ((rOf T M ⊔ qOf T).relIndex
      (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))) = 3 := by
    have h3 : ((rOf T M ⊔ qOf T).relIndex
        (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))) * 4 = 12 := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc _ = ((rOf T M ⊔ qOf T).relIndex
            (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))) * (4 * Nat.card ↥(qOf T)) := by
              ring
        _ = 12 * Nat.card ↥(qOf T) := h1
    omega
  change ¬ 2 ∣ (rOf T M ⊔ qOf T).relIndex
    (mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G))
  rw [h2]
  decide

theorem Counter.isSylowTwoOf_rq_normalizer_Ac :
    IsSylowTwoOf (rOf T M ⊔ qOf T) (Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) := by
  have hRQN : rOf T M ⊔ qOf T ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    (sup_le_sup_right (pCoreOf_le 2 (iTwo T M)) _).trans (c.normal_Ac hrW hrV hr2)
  have hRQH : rOf T M ⊔ qOf T ≤ mcOf T :=
    sup_le (rOf_le_mcOf c) (pCoreOf_le 2 (mcOf T))
  have hP2 : IsPGroup 2 ↥(rOf T M ⊔ qOf T) := c.hyp.sylow.1.to_le (rq_le_of_hyp c.h1281)
  obtain ⟨S, hRS, hS⟩ := exists_isSylowTwoOf_of_le hRQN hP2
  by_cases heq : S = rOf T M ⊔ qOf T
  · rw [← heq]; exact hS
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, ⟨hxS, hxNP⟩, hxn⟩ :=
    exists_mem_inf_normalizer_of_ne (p := 2) hS.isPGroup hRS (Ne.symm heq)
  have hxA : x ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := hS.le hxS
  have hZA : quasithinOmegaOneCenter T ≤ c.Ac hrW hrV hr2 := fun z hz =>
    c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hz)
  have hxZ : ∀ z ∈ quasithinOmegaOneCenter T, x * z * x⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro z hz
    apply c.inf_centralizer_rq_le hrW hrV hr2
    refine ⟨(Subgroup.mem_normalizer_iff.mp hxA z).mp (hZA hz), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro p hp
    have hp' : x⁻¹ * p * x ∈ rOf T M ⊔ qOf T := by
      refine (Subgroup.mem_normalizer_iff.mp hxNP (x⁻¹ * p * x)).mpr ?_
      have e : x * (x⁻¹ * p * x) * x⁻¹ = p := by group
      rw [e]; exact hp
    have hzc : z * (x⁻¹ * p * x) = (x⁻¹ * p * x) * z :=
      Subgroup.mem_centralizer_iff.mp (hRQH hp') z hz
    calc p * (x * z * x⁻¹) = x * ((x⁻¹ * p * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * p * x)) * x⁻¹ := by rw [hzc]
      _ = (x * z * x⁻¹) * p := by group
  have hxH : x ∈ mcOf T := by
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp
      c.h1281.card_omegaOneCenter
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · have h1 : (⟨x * z * x⁻¹, hxZ z hz⟩ : ↥(quasithinOmegaOneCenter T)) ≠ 1 := by
        intro he
        have : x * z * x⁻¹ = 1 := congrArg Subtype.val he
        apply hz1
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = 1 := by rw [this]; group
      have h2 : (⟨z, hz⟩ : ↥(quasithinOmegaOneCenter T)) ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
      have h3 := (hw _ h1).trans (hw _ h2).symm
      have h4 : x * z * x⁻¹ = z := congrArg Subtype.val h3
      calc z * x = (x * z * x⁻¹) * x := by rw [h4]
        _ = x * z := by group
  have hSyl := c.isSylowTwoOf_rq_inf_normalizer_Ac hrW hrV hr2
  have hVle : rOf T M ⊔ qOf T ⊔ Subgroup.zpowers x ≤
      mcOf T ⊓ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    sup_le (le_inf hRQH hRQN) ((Subgroup.zpowers_le).2 ⟨hxH, hxA⟩)
  have hVS : rOf T M ⊔ qOf T ⊔ Subgroup.zpowers x ≤ S :=
    sup_le hRS ((Subgroup.zpowers_le).2 hxS)
  have hV2 : IsPGroup 2 ↥(rOf T M ⊔ qOf T ⊔ Subgroup.zpowers x) := hS.isPGroup.to_le hVS
  have heqV := hSyl.eq_of_le le_sup_left hVle hV2
  apply hxn
  rw [← heqV]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

end Centralizer

end S143

end CFSG.Quasithin
