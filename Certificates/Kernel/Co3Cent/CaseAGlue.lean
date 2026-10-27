module

public import Certificates.Kernel.Co3Cent.CaseBGlue
public import Certificates.Kernel.Co3Cent.CentAChk
public import Certificates.Kernel.Co3Cent.CaseCGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co3Cent Subgroup
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.RankThree.Native (permsA)
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CFSG.HardMathSupport.Dickson.I271.Co3Cent (rGens)

@[expose] noncomputable def xA : Equiv.Perm (Fin 276) := pv xAp

theorem permXA : permB 276 9 xAp = true := permDG (j := 2) (by norm_num)

theorem prepXA : PRep 276 9 xAp xA := prep_pv permXA

theorem xA_mem : xA ∈ co3P :=
  (dv_facts (j := 2) (by norm_num)).1

theorem xaFacts : fixSetK 276 9 511 xAp (BA.take 6) = true ∧ powIdK 276 9 511 xAp 3 = true ∧
    movesK 276 9 511 xAp = true ∧ Nat.blt JK 17 = true ∧ Nat.beq fld(getS MA 6, JK, 1) 1 = true ∧
    (!(commOK 276 9 511 (getS SA JK) xAp)) = true := by
  have h := ch17370_xa
  simp only [bAnd_iff] at h
  exact h

theorem xA_pow : xA ^ 3 = 1 := pow_eq_one_of_powIdK xaFacts.2.1 prepXA

theorem xA_ne : xA ≠ 1 := ne_one_of_movesK xaFacts.2.2.1 prepXA

theorem xA_eq : permOfArr 276 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.dElts ())[
    CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.kA]! = xA := by
  rw [show CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.kA = 9 from rfl,
    CertificateChecks.KernelCo3T.E_get (by norm_num)]
  rfl

theorem take6 : BA.take 6 = List.ofFn (fun t : Fin 6 => getS BA t) := by decide +kernel

@[expose] noncomputable def FA (t : Fin 6) : Fin 276 := bA t

theorem fixA : ∀ i, xA i = i ↔ i ∈ Set.range FA := by
  intro i
  have h1 := fixSetK_sound xaFacts.1 i.2
  have e : pg 9 511 xAp i = xA i := prepXA i
  rw [e, take6, List.mem_ofFn] at h1
  rw [Fin.ext_iff, h1]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Fin.ext ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

theorem fixA_lt {t : ℕ} (ht : t < 6) : xA (bA t) = bA t := (fixA _).2 ⟨⟨t, ht⟩, rfl⟩

theorem prodKA6 : ∏ t ∈ Finset.Ico 6 11, getS KA t = 972 := by decide +kernel

theorem prodKA11 : ∏ t ∈ Finset.Ico 11 11, getS KA t = 1 := by decide +kernel

theorem KA_eq :
    Gv SA MA 17 6 = stabB co3P bA 6 := (chainA 6 (by norm_num)).1

theorem card_KA :
    Nat.card (Gv SA MA 17 6) = 972 := by rw [(chainA 6 (by norm_num)).2, prodKA6]

theorem memK_iff
    (g : Equiv.Perm (Fin 276)) : g ∈ Gv SA MA 17 6 ↔ g ∈ co3P ∧ ∀ t, g (FA t) = FA t := by
  rw [KA_eq, mem_stabB]
  constructor
  · rintro ⟨hP, hf⟩
    exact ⟨hP, fun t => hf t t.2⟩
  · rintro ⟨hP, hf⟩
    exact ⟨hP, fun t ht => hf ⟨t, ht⟩⟩

theorem eq_one_of_fixA
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3P) (hfix : ∀ t < 11, g (bA t) = bA t) : g = 1 := by
  have h := chainA 11 le_rfl
  rw [prodKA11] at h
  have hm : g ∈ Gv SA MA 17 11 := by
    rw [h.1]
    exact ⟨hg, hfix⟩
  have h1 : Nat.card (Gv SA MA 17 11) = 1 := h.2
  rw [Subgroup.eq_bot_of_card_eq _ h1] at hm
  exact (mem_bot).1 hm

theorem raFacts : allN 5 (fun j => bAnd(inCA (RGp j), fixFA (RGp j))) = true ∧
    allN 5 (fun i => allN 5 fun j =>
      zMulAK (pcomp 276 9 511 (RGp i) (RGp j)) (pcomp 276 9 511 (RGp j) (RGp i))) = true := by
  have h := ch17370_ra
  simp only [bAnd_iff] at h
  exact h

@[expose] noncomputable def rv (j : ℕ) : Equiv.Perm (Fin 276) := pv (RGp j)

theorem rv_facts {j : ℕ}
    (hj : j < 5) : permB 276 9 (RGp j) = true ∧ rv j ∈ co3P ∧ rv j * xA = xA * rv j :=
  inC_spec permXA ((bAnd_iff _ _).1 (allN_spec raFacts.1 j hj)).1

theorem permRG {j : ℕ} (hj : j < 5) : permB 276 9 (RGp j) = true :=
  (inP3K_spec ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (allN_spec raFacts.1 j hj)).1).1).1

theorem prepRG {j : ℕ} (hj : j < 5) : PRep 276 9 (RGp j) (rv j) := prep_pv (permRG hj)

theorem rv_fixF {j : ℕ} (hj : j < 5) : ∀ t, rv j (FA t) = FA t := by
  intro t
  have h := ((bAnd_iff _ _).1 (allN_spec raFacts.1 j hj)).2
  unfold fixFA at h
  have h1 := allN_spec h t t.2
  rw [strictB_apply] at h1
  apply Fin.ext
  rw [← (prepRG hj (FA t))]
  exact Nat.eq_of_beq_eq_true h1

theorem rGens_get {j : ℕ} (hj : j < 5) : (rGens ())[j]! = unpack 276 9 (RGp j) := by
  unfold rGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact arr_eq _ (by omega)

theorem rGens_size : (rGens ()).size = 5 := by simp [rGens]

theorem permsA_R : permsA 276 (rGens ()) = Set.range (fun j : Fin 5 => rv j) := by
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj5 : j < 5 := by rw [← rGens_size]; exact hj
    refine ⟨⟨j, hj5⟩, ?_⟩
    change pv (RGp j) = permOfArr 276 (rGens ())[j]!
    rw [pv, rGens_get hj5]
  · rintro ⟨j, rfl⟩
    refine ⟨j.val, by change j.val < (rGens ()).size; rw [rGens_size]; exact j.2, ?_⟩
    change permOfArr 276 (rGens ())[j.val]! = pv (RGp j.val)
    rw [pv, rGens_get j.2]

@[expose] noncomputable def RA : Subgroup (Equiv.Perm (Fin 276)) := closure (permsA 276 (rGens ()))

theorem RA_eq : RA = closure (Set.range fun j : Fin 5 => rv j) := by rw [RA, permsA_R]

theorem rv_mem_RA {j : ℕ} (hj : j < 5) : rv j ∈ RA := by
  rw [RA_eq]
  exact subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem RA_le :
    RA ≤ Gv SA MA 17 6 := by
  rw [RA_eq]
  refine (closure_le _).2 (Set.range_subset_iff.2 fun j => ?_)
  exact (memK_iff _).2 ⟨(rv_facts j.2).2.1, rv_fixF j.2⟩

theorem RA_C :
    RA ≤ centralizer {xA} ⊓ co3P := by
  rw [RA_eq]
  refine (closure_le _).2 (Set.range_subset_iff.2 fun j => ?_)
  have h1 := rv_facts j.2
  refine Subgroup.mem_inf.2 ⟨?_, h1.2.1⟩
  rw [mem_centralizer_singleton_iff]
  exact h1.2.2

@[expose] noncomputable def vR (i : Fin 5) : Fin 276 := bA (6 + i)

theorem hvR : ∀ i : Fin 5, getS BA (6 + i) = vR i := fun _ => rfl

theorem rkFacts : orbRecK rActA (revKey 9 511 5) 5 16 65535 (subKey 9 BA 6 5) 243 RK RR = true ∧
    memK (mapKey 9 511 xAp 5 (subKey 9 BA 6 5)) RK = true := by
  have h := ch17370_rk
  simp only [bAnd_iff] at h
  exact h

theorem recR : RK.length = 243 ∧ (RK.map (revKey 9 511 5)).Nodup ∧
    (0 < 243 → subKey 9 BA 6 5 ∈ RK) ∧ (∀ e ∈ RK, ∀ j < 5, rActA j e ∈ RK) ∧
    ∀ e ∈ RK, ActReach rActA 5 (subKey 9 BA 6 5) e :=
  orbRecK_sound rkFacts.1

theorem rAct_tkey {j : ℕ} (hj : j < 5) (u : Fin 5 → Fin 276) :
    rActA j (tkey 9 u) = tkey 9 (fun i => rv j (u i)) :=
  mapKey_tkey (by norm_num) (prepRG hj) u

theorem reachR : ∀ e, ActReach rActA 5 (subKey 9 BA 6 5) e →
    ∃ r ∈ RA, e = tkey 9 (fun i => r (vR i)) := by
  intro e he
  induction he with
  | root =>
    refine ⟨1, one_mem _, ?_⟩
    rw [subKey_tkey hvR]
    rfl
  | @step e j _ hj ih =>
    obtain ⟨r, hr, rfl⟩ := ih
    refine ⟨rv j * r, mul_mem (rv_mem_RA hj) hr, ?_⟩
    rw [rAct_tkey hj]
    rfl

@[expose] noncomputable def ER : Finset (Fin 5 → Fin 276) :=
  Finset.univ.filter fun u => tkey 9 u ∈ RK

theorem mem_ER {u : Fin 5 → Fin 276} : u ∈ ER ↔ tkey 9 u ∈ RK := by
  simp [ER]

theorem card_ER : ER.card = 243 := by
  have himg : ER.image (tkey 9) = RK.toFinset := by
    ext k
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_ER.1 hu
    · intro hk
      obtain ⟨r, -, rfl⟩ := reachR k (recR.2.2.2.2 k hk)
      exact ⟨_, mem_ER.2 hk, rfl⟩
  rw [← Finset.card_image_of_injective _ (fun u u' h => tkey_inj (w := 9) (by norm_num) h), himg,
    List.toFinset_card_of_nodup (List.Nodup.of_map _ recR.2.1), recR.1]

theorem fixR_eq_one :
    ∀ g ∈ Gv SA MA 17 6, (∀ i, g (vR i) = vR i) → g = 1 := by
  intro g hg hv
  rw [KA_eq, mem_stabB] at hg
  refine eq_one_of_fixA hg.1 fun t ht => ?_
  rcases Nat.lt_or_ge t 6 with h6 | h6
  · exact hg.2 t h6
  · have h := hv ⟨t - 6, by omega⟩
    have e : 6 + (t - 6) = t := by omega
    simp only [vR, e] at h
    exact h

theorem keyR_facts :
    Nat.card RA = ER.card ∧ ∀ y ∈ Gv SA MA 17 6, (fun i => y (vR i)) ∈ ER → y ∈ RA :=
  key_orbit RA_eq RA_le vR fixR_eq_one ER
    (mem_ER.2 (by rw [← subKey_tkey hvR]; exact recR.2.2.1 (by norm_num)))
    (by
      rintro e he _ ⟨j, rfl⟩
      have h := recR.2.2.2.1 _ (mem_ER.1 he) j j.2
      rw [rAct_tkey j.2] at h
      exact mem_ER.2 h)
    (by
      intro e he
      obtain ⟨r, hr, he'⟩ := reachR _ (recR.2.2.2.2 _ (mem_ER.1 he))
      exact ⟨r, hr, (tkey_inj (w := 9) (by norm_num) he').symm⟩)

theorem card_RA :
    Nat.card RA = 243 := by
  rw [keyR_facts.1, card_ER]

end CertificateChecks.KernelCo3Cent

end
