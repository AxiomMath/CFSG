module

public import CFSG.Quasithin.EmptyFaithful.S143KK
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.Quasithin.EmptyFaithful.S143GC
public import CFSG.Quasithin.EmptyFaithful.S143KJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

theorem I4_mm (M : Mat4) : mm I4 M = M := by
  obtain ⟨r0, r1, r2, r3⟩ := M
  show (⟨vm I4.r0 ⟨r0, r1, r2, r3⟩, vm I4.r1 ⟨r0, r1, r2, r3⟩, vm I4.r2 ⟨r0, r1, r2, r3⟩,
    vm I4.r3 ⟨r0, r1, r2, r3⟩⟩ : Mat4) = ⟨r0, r1, r2, r3⟩
  rw [show I4.r0 = ⟨true, false, false, false⟩ from rfl, show I4.r1 = ⟨false, true, false, false⟩ from rfl,
    show I4.r2 = ⟨false, false, true, false⟩ from rfl, show I4.r3 = ⟨false, false, false, true⟩ from rfl,
    vm_e0, vm_e1, vm_e2, vm_e3]

section Comm

variable {G : Type*} [Group G]

@[expose] def commSub (A : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ Subgroup.normalizer (A : Set G) ∧
    ∀ γ ∈ Subgroup.centralizer (A : Set G), k * γ * k⁻¹ * γ⁻¹ ∈ A}
  mul_mem' := by
    rintro k₁ k₂ ⟨hk₁, h₁⟩ ⟨hk₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hk₁ hk₂, fun γ hγ => ?_⟩
    have h1 := h₁ (k₂ * γ * k₂⁻¹) (centralizer_conj_mem hk₂ hγ)
    have h2 := h₂ γ hγ
    have e : k₁ * k₂ * γ * (k₁ * k₂)⁻¹ * γ⁻¹ =
        (k₁ * (k₂ * γ * k₂⁻¹) * k₁⁻¹ * (k₂ * γ * k₂⁻¹)⁻¹) * (k₂ * γ * k₂⁻¹ * γ⁻¹) := by group
    rw [e]
    exact A.mul_mem h1 h2
  one_mem' := ⟨Subgroup.one_mem _, fun γ _ => by simp [A.one_mem]⟩
  inv_mem' := by
    rintro k ⟨hk, h⟩
    refine ⟨(Subgroup.normalizer _).inv_mem hk, fun γ hγ => ?_⟩
    have h1 := h (k⁻¹ * γ * k) (by
      have := centralizer_conj_mem ((Subgroup.normalizer _).inv_mem hk) hγ
      simpa using this)
    have e : k⁻¹ * γ * k⁻¹⁻¹ * γ⁻¹ = (k * (k⁻¹ * γ * k) * k⁻¹ * (k⁻¹ * γ * k)⁻¹)⁻¹ := by group
    rw [e]
    exact A.inv_mem h1

theorem commSub_conj_mem {A : Subgroup G} {k s : G} (hk : k ∈ Subgroup.normalizer (A : Set G))
    (hs : s ∈ commSub A) : k * s * k⁻¹ ∈ commSub A := by
  obtain ⟨hsN, hs'⟩ := hs
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hsN) ((Subgroup.normalizer _).inv_mem hk),
    fun γ hγ => ?_⟩
  have h1 := hs' (k⁻¹ * γ * k) (by
    have := centralizer_conj_mem ((Subgroup.normalizer _).inv_mem hk) hγ
    simpa using this)
  have h2 : k * (s * (k⁻¹ * γ * k) * s⁻¹ * (k⁻¹ * γ * k)⁻¹) * k⁻¹ ∈ A :=
    conj_mem_of_mem_normalizer hk h1
  have e : k * s * k⁻¹ * γ * (k * s * k⁻¹)⁻¹ * γ⁻¹ =
      k * (s * (k⁻¹ * γ * k) * s⁻¹ * (k⁻¹ * γ * k)⁻¹) * k⁻¹ := by group
  rw [e]
  exact h2

end Comm

section Gamma

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.centralizer_Ac_le_rq :
    Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ≤ rOf T M ⊔ qOf T := by
  have hN : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) : Set G) := fun k hk =>
    mem_normalizer_of_conj_mem (fun x hx => centralizer_conj_mem hk hx) (fun x hx => by
      have := centralizer_conj_mem ((Subgroup.normalizer _).inv_mem hk) hx
      simpa using this)
  have h1 : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ≤
      pCoreOf 2 (Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.centralizer_le_normalizer (c.Ac hrW hrV hr2 : Set G)) hN
      (c.isPGroup_centralizer_Ac hrW hrV hr2)
  exact h1.trans (c.isSylowTwoOf_rq_normalizer_Ac hrW hrV hr2).pCoreOf_le

end Gamma

section KComm

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ

theorem Setup.exists_w : ∃ w ∈ Hyp1281Two.wOfU T M, w ∉ c.Ac hrW hrV hr2 ∧
    cmat z a r r1 w ≠ I4 := by
  have hB := hS.basis
  obtain ⟨w, hwW, hwA⟩ : ∃ w ∈ Hyp1281Two.wOfU T M, w ∉ c.Ac hrW hrV hr2 := by
    by_contra hh
    push Not at hh
    have h1 : Nat.card (Hyp1281Two.wOfU T M) ≤ Nat.card ↥(c.Ac hrW hrV hr2 ⊓ qOf T) :=
      Subgroup.card_le_of_le fun x hx => ⟨hh x hx, c.wOfU_le_qOf hx⟩
    have hW : Nat.card ↥(Hyp1281Two.wOfU T M) = 16 := card_wOf c
    rw [hW, c.card_inf_qOf_Ac hrW hrV hr2] at h1
    omega
  refine ⟨w, hwW, hwA, fun h => hwA ?_⟩
  have hwR : w ∈ rOf T M := c.mem_rOf_of_mem_wOfU hwW
  have hRC := c.centralizer_inf_rOf_Ac hrW hrV hr2 htT htRQ
  have : w ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M :=
    ⟨(hB.cmat_eq_one_iff_mem_centralizer
      (c.rOf_le_normalizer_Ac hrW hrV hr2 hwR)).mp h, hwR⟩
  rwa [hRC] at this

variable {y : G} {cm : Mat4} (hM : KModel hS cm y)

include hM

theorem Setup.K_le_commSub : kOf T M (c.Ac hrW hrV hr2) ≤ commSub (c.Ac hrW hrV hr2) := by
  have hB := hS.basis
  have hKN : kOf T M (c.Ac hrW hrV hr2) ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    c.kOf_le_normalizer_Ac hrW hrV hr2
  have hK := hM.K_le
  have hRUK := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hΓ2 := c.isPGroup_centralizer_Ac hrW hrV hr2
  set S : Subgroup G := commSub (c.Ac hrW hrV hr2) ⊓ kOf T M (c.Ac hrW hrV hr2) with hSdef
  have hSK : S ≤ kOf T M (c.Ac hrW hrV hr2) := inf_le_right
  have hKS : kOf T M (c.Ac hrW hrV hr2) ≤ Subgroup.normalizer (S : Set G) := by
    intro k hk
    refine mem_normalizer_of_conj_mem (fun s hs => ?_) (fun s hs => ?_)
    · exact ⟨commSub_conj_mem (hKN hk) hs.1,
        (kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem hk hs.2)
          ((kOf T M (c.Ac hrW hrV hr2)).inv_mem hk)⟩
    · have h1 := commSub_conj_mem (hKN ((kOf T M (c.Ac hrW hrV hr2)).inv_mem hk)) hs.1
      rw [inv_inv] at h1
      exact ⟨h1, (kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem
        ((kOf T M (c.Ac hrW hrV hr2)).inv_mem hk) hs.2) hk⟩
  have hΓH := c.centralizer_Ac_le_mcOf hrW hrV hr2
  have hΓT : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ≤ T :=
    (c.centralizer_Ac_le_rq hrW hrV hr2).trans (rq_le_of_hyp c.h1281)
  have hUS : uOfL22 T M ≤ S := by
    intro u hu
    have huN : u ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
      c.iTwo_le_normalizer_Ac hrW hrV hr2 (le_conjClosure _ _ hu)
    refine ⟨⟨huN, fun γ hγ => ?_⟩, hRUK (Subgroup.mem_sup_right hu)⟩
    have h1 : γ * u⁻¹ * γ⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (c.hHU (hΓH hγ)) u⁻¹).mp ((uOfL22 T M).inv_mem hu)
    have h2 : u * γ * u⁻¹ * γ⁻¹ ∈ uOfL22 T M := by
      have e : u * γ * u⁻¹ * γ⁻¹ = u * (γ * u⁻¹ * γ⁻¹) := by group
      rw [e]; exact (uOfL22 T M).mul_mem hu h1
    have h3 : u * γ * u⁻¹ * γ⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
      Subgroup.mul_mem _ (centralizer_conj_mem huN hγ) (Subgroup.inv_mem _ hγ)
    exact c.centralizer_inf_uOfL22_le_Ac hrW hrV hr2 htT htRQ h2 h3
  have hRS : rOf T M ≤ S := by
    intro ρ hρ
    have hρN := c.rOf_le_normalizer_Ac hrW hrV hr2 hρ
    refine ⟨⟨hρN, fun γ hγ => ?_⟩, hRUK (Subgroup.mem_sup_left hρ)⟩
    have h1 : γ * ρ⁻¹ * γ⁻¹ ∈ rOf T M :=
      (Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer_rOf' (hΓT hγ)) ρ⁻¹).mp
        ((rOf T M).inv_mem hρ)
    have h2 : ρ * γ * ρ⁻¹ * γ⁻¹ ∈ rOf T M := by
      have e : ρ * γ * ρ⁻¹ * γ⁻¹ = ρ * (γ * ρ⁻¹ * γ⁻¹) := by group
      rw [e]; exact (rOf T M).mul_mem hρ h1
    have h3 : ρ * γ * ρ⁻¹ * γ⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
      Subgroup.mul_mem _ (centralizer_conj_mem hρN hγ) (Subgroup.inv_mem _ hγ)
    have := c.centralizer_inf_rOf_Ac hrW hrV hr2 htT htRQ
    rw [← this]
    exact ⟨h3, h2⟩
  have hnormS : (S.subgroupOf (kOf T M (c.Ac hrW hrV hr2))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).mpr hKS
  have hsurj := homK_surjective hB hM.inj hK hM.x_K hM.y_K hM.count
  have hN'norm : ((S.subgroupOf (kOf T M (c.Ac hrW hrV hr2))).map (homK hB hM.inj hK)).Normal :=
    hnormS.map _ hsurj
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  obtain ⟨w, hwW, hwA, hwne⟩ := hS.exists_w htT htRQ
  have hwR : w ∈ rOf T M := c.mem_rOf_of_mem_wOfU hwW
  have hwK : w ∈ kOf T M (c.Ac hrW hrV hr2) := hRUK (Subgroup.mem_sup_left hwR)
  have hwS : (⟨w, hwK⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) ∈
      S.subgroupOf (kOf T M (c.Ac hrW hrV hr2)) := hRS hwR
  have hqw : homK hB hM.inj hK ⟨w, hwK⟩ ≠ 1 := fun h =>
    hwne ((homK_eq_one_iff hB hM.inj hK ⟨w, hwK⟩).mp h)
  have htop : (S.subgroupOf (kOf T M (c.Ac hrW hrV hr2))).map (homK hB hM.inj hK) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((S.subgroupOf (kOf T M (c.Ac hrW hrV hr2))).map (homK hB hM.inj hK)) with h | h
    · exfalso
      apply hqw
      have : homK hB hM.inj hK ⟨w, hwK⟩ ∈
          (S.subgroupOf (kOf T M (c.Ac hrW hrV hr2))).map (homK hB hM.inj hK) :=
        ⟨⟨w, hwK⟩, hwS, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · exact h
  have hpow : ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), ∃ m : ℕ, k ^ 2 ^ m ∈ S := by
    intro k hk
    have hmem : homK hB hM.inj hK ⟨k, hk⟩ ∈
        (S.subgroupOf (kOf T M (c.Ac hrW hrV hr2))).map (homK hB hM.inj hK) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨s', hs', hs'k⟩ := hmem
    set s : G := (s' : G) with hs
    have hsS : s ∈ S := hs'
    have hsK : s ∈ kOf T M (c.Ac hrW hrV hr2) := s'.2
    set c' : G := k * s⁻¹ with hc'
    have hc'K : c' ∈ kOf T M (c.Ac hrW hrV hr2) :=
      (kOf T M (c.Ac hrW hrV hr2)).mul_mem hk ((kOf T M (c.Ac hrW hrV hr2)).inv_mem hsK)
    have hc'Γ : c' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := by
      have h1 : homK hB hM.inj hK ⟨c', hc'K⟩ = 1 := by
        have e : (⟨c', hc'K⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) = ⟨k, hk⟩ * s'⁻¹ := rfl
        rw [e, map_mul, map_inv, hs'k]; exact mul_inv_cancel _
      exact (hB.cmat_eq_one_iff_mem_centralizer (hKN hc'K)).mp
        ((homK_eq_one_iff hB hM.inj hK ⟨c', hc'K⟩).mp h1)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hΓ2) ⟨c', hc'Γ⟩
    have hcm : c' ^ 2 ^ m = 1 := by
      have := pow_orderOf_eq_one (⟨c', hc'Γ⟩ : ↥(Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)))
      rw [hm] at this
      exact congrArg Subtype.val this
    have hkc : k = c' * s := by rw [hc']; group
    have key : ∀ j : ℕ, ∃ sj ∈ S, (c' * s) ^ j = c' ^ j * sj := by
      intro j
      induction j with
      | zero => exact ⟨1, S.one_mem, by simp⟩
      | succ j ih =>
        obtain ⟨sj, hsj, hj⟩ := ih
        have hconj : c'⁻¹ * sj * c'⁻¹⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp
            (hKS ((kOf T M (c.Ac hrW hrV hr2)).inv_mem hc'K)) sj).mp hsj
        refine ⟨c'⁻¹ * sj * c'⁻¹⁻¹ * s, S.mul_mem hconj hsS, ?_⟩
        rw [pow_succ, hj, pow_succ]
        group
    obtain ⟨sj, hsj, hj⟩ := key (2 ^ m)
    refine ⟨m, ?_⟩
    rw [hkc, hj, hcm, one_mul]
    exact hsj
  have hKS' : kOf T M (c.Ac hrW hrV hr2) ≤ S := by
    have := oTwoUpper_le_of_pow_mem hpow
    rwa [oTwoUpper_kOf] at this
  exact fun k hk => (hKS' hk).1

end KComm

end S143

end CFSG.Quasithin
