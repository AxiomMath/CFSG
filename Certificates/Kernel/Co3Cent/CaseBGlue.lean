module

public import Certificates.Kernel.Co3Cent.ChainGlue
public import Certificates.Kernel.Co3Cent.CentBChk
public import Certificates.Kernel.Co3T.Facts
public import CFSG.Certificates.Kernel.OrbRow.KeyOrbit
public import CFSG.Certificates.Kernel.OrbRow.WordRep
public import CFSG.Certificates.Kernel.Co3Cent.Bound
public import CFSG.Certificates.Kernel.Co3Cent.Sylow
public import Certificates.Data.Co3Cent
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co3Cent Subgroup
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.RankThree.Native (permsA)
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

theorem inC_spec {g xp : ℕ}
    (hx : permB 276 9 xp = true)
    (h : bAnd(inP3K (List.cons g List.nil) 0, commOK 276 9 511 g xp) = true) :
    permB 276 9 g = true ∧ pv g ∈ co3P ∧ pv g * pv xp = pv xp * pv g := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have e : getS (List.cons g List.nil) 0 = g := rfl
  have hp : permB 276 9 g = true := e ▸ (inP3K_spec h1).1
  have h3 : pv (getS (List.cons g List.nil) 0) ∈ co3P := pv_mem h1
  rw [e] at h3
  have h2' : commOK 276 9 (mask 9) g xp = true := h2
  exact ⟨hp, h3, (commOK_iff (prep_pv hp) (prep_pv hx)).1 h2'⟩

theorem dFacts : allN 5 (fun j => inCB (DGp j)) = true ∧
    allN 6 (fun t => Nat.beq (getS KPB t) (getS BB t)) = true ∧
    Nat.beq (getS KPB 6) (getS BB 15) = true ∧
    orbRecK dActB (revKey 9 511 7) 5 16 65535 (subKey 9 KPB 0 7) 243 DK DR = true := by
  have h := ch17370_d
  simp only [bAnd_iff] at h
  exact h

theorem xbFacts : fixSetK 276 9 511 xBp (BB.take 15) = true ∧ powIdK 276 9 511 xBp 3 = true ∧
    movesK 276 9 511 xBp = true := by
  have h := ch17370_xb
  simp only [bAnd_iff] at h
  exact h

theorem permDG {j : ℕ} (hj : j < 5) : permB 276 9 (DGp j) = true :=
  (inP3K_spec ((bAnd_iff _ _).1 (allN_spec dFacts.1 j hj)).1).1

theorem permXB : permB 276 9 xBp = true := permDG (j := 0) (by norm_num)

@[expose] noncomputable def xB : Equiv.Perm (Fin 276) := pv xBp

@[expose] noncomputable def dv (j : ℕ) : Equiv.Perm (Fin 276) := pv (DGp j)

theorem prepXB : PRep 276 9 xBp xB := prep_pv permXB

theorem prepD {j : ℕ} (hj : j < 5) : PRep 276 9 (DGp j) (dv j) := prep_pv (permDG hj)

theorem dv_facts {j : ℕ} (hj : j < 5) :
    dv j ∈ co3P ∧ dv j * xB = xB * dv j :=
  (inC_spec permXB (allN_spec dFacts.1 j hj)).2

theorem xB_mem : xB ∈ co3P :=
  (dv_facts (j := 0) (by norm_num)).1

theorem xB_pow : xB ^ 3 = 1 := pow_eq_one_of_powIdK xbFacts.2.1 prepXB

theorem xB_ne : xB ≠ 1 := ne_one_of_movesK xbFacts.2.2 prepXB

theorem xB_eq : permOfArr 276
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.dElts ())[1]! = xB := by
  rw [CertificateChecks.KernelCo3T.E_get (by norm_num)]
  rfl

theorem DGp_eqK : allN 5 (fun j => Nat.beq (DGp j) (CertificateChecks.KernelCo3T.TT.L (4 + j))) =
    true := by
  quickRfl

theorem dGens_get {j : ℕ} (hj : j < 5) : (dGens ())[j]! = unpack 276 9 (DGp j) := by
  rw [CertificateChecks.KernelCo3T.dg_get hj, Nat.eq_of_beq_eq_true (allN_spec DGp_eqK j hj)]

theorem dGens_size : (dGens ()).size = 5 := by simp [dGens]

theorem permsA_D : permsA 276 (dGens ()) = Set.range (fun j : Fin 5 => dv j) := by
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj5 : j < 5 := by rw [← dGens_size]; exact hj
    refine ⟨⟨j, hj5⟩, ?_⟩
    change pv (DGp j) = permOfArr 276 (dGens ())[j]!
    rw [pv, dGens_get hj5]
  · rintro ⟨j, rfl⟩
    refine ⟨j.val, by change j.val < (dGens ()).size; rw [dGens_size]; exact j.2, ?_⟩
    change permOfArr 276 (dGens ())[j.val]! = pv (DGp j.val)
    rw [pv, dGens_get j.2]

@[expose] noncomputable def DB : Subgroup (Equiv.Perm (Fin 276)) :=
  closure (permsA 276 (dGens ()))

theorem DB_eq : DB = closure (Set.range fun j : Fin 5 => dv j) := by rw [DB, permsA_D]

theorem dv_mem_DB {j : ℕ} (hj : j < 5) : dv j ∈ DB := by
  rw [DB_eq]
  exact subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem DB_le :
    DB ≤ centralizer {xB} ⊓ co3P := by
  rw [DB_eq]
  refine (closure_le _).2 (Set.range_subset_iff.2 fun j => ?_)
  have h1 : dv j.val ∈ co3P ∧ dv j.val * xB = xB * dv j.val := dv_facts j.2
  refine Subgroup.mem_inf.2 ⟨?_, h1.1⟩
  rw [mem_centralizer_singleton_iff]
  exact h1.2

theorem DB_ab : ∀ a ∈ DB, ∀ b ∈ DB, a * b = b * a := by
  have hg : ∀ i < 5, ∀ j < 5, dv i * dv j = dv j * dv i := by
    intro i hi j hj
    have hc := Nat.eq_of_beq_eq_true
      (allN_spec (allN_spec CertificateChecks.KernelCo3T.kD4.1.1.2 i hi) j hj)
    have e : ∀ l < 5, CertificateChecks.KernelCo3T.TT.L (4 + l) = DGp l := fun l hl =>
      (Nat.eq_of_beq_eq_true (allN_spec DGp_eqK l hl)).symm
    rw [e i hi, e j hj] at hc
    have h1 := prep_pcomp (by norm_num) (prepD hi) (prepD hj)
    have h2 := prep_pcomp (by norm_num) (prepD hj) (prepD hi)
    change PRep 276 9 (CFSG.KC.B3S3K.cm 276 9 (DGp i) (DGp j)) _ at h1
    rw [hc] at h1
    exact CFSG.KC.OrbRow.prep_unique h1 h2
  have hZ : ∀ z ∈ (⊥ : Subgroup (Equiv.Perm (Fin 276))), ∀ g, z * g = g * z := by
    intro z hz g
    rw [(mem_bot).1 hz, one_mul, mul_one]
  have h := CFSG.KC.Co3Cent.comm_mem_of_gens (Y := Set.range fun j : Fin 5 => dv j)
    (fun z hz g _ => hZ z hz g) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [hg i i.2 j j.2, mem_bot]
    group)
  intro a ha b hb
  rw [DB_eq] at ha hb
  have := (mem_bot).1 (h a ha b hb)
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

theorem take15 : BB.take 15 = List.ofFn (fun t : Fin 15 => getS BB t) := by decide +kernel

@[expose] noncomputable def FB (t : Fin 15) : Fin 276 := bB t

theorem fixB : ∀ i, xB i = i ↔ i ∈ Set.range FB := by
  intro i
  have h1 := fixSetK_sound xbFacts.1 i.2
  have e : pg 9 511 xBp i = xB i := prepXB i
  rw [e, take15, List.mem_ofFn] at h1
  rw [Fin.ext_iff, h1]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Fin.ext ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

theorem fixB_lt {t : ℕ} (ht : t < 15) : xB (bB t) = bB t := (fixB _).2 ⟨⟨t, ht⟩, rfl⟩

theorem b15_ne : ∀ t : Fin 15, getS BB t ≠ getS BB 15 := by decide +kernel

theorem xB_b15 : xB (bB 15) ≠ bB 15 := by
  intro h
  obtain ⟨t, ht⟩ := (fixB _).1 h
  exact b15_ne t (congrArg Fin.val ht)

theorem KPB_lt : ∀ i : Fin 7, getS KPB i < 276 := by decide

@[expose] noncomputable def vD (i : Fin 7) : Fin 276 := ⟨getS KPB i, KPB_lt i⟩

theorem hvD : ∀ i : Fin 7, getS KPB (0 + i) = vD i := fun i => by
  rw [Nat.zero_add]
  rfl

theorem vD_lt {t : ℕ} (ht : t < 6) : vD ⟨t, by omega⟩ = bB t :=
  Fin.ext (Nat.eq_of_beq_eq_true (allN_spec dFacts.2.1 t ht))

theorem vD6 : vD 6 = bB 15 := Fin.ext (Nat.eq_of_beq_eq_true dFacts.2.2.1)

theorem recD : DK.length = 243 ∧ (DK.map (revKey 9 511 7)).Nodup ∧
    (0 < 243 → subKey 9 KPB 0 7 ∈ DK) ∧ (∀ e ∈ DK, ∀ j < 5, dActB j e ∈ DK) ∧
    ∀ e ∈ DK, ActReach dActB 5 (subKey 9 KPB 0 7) e :=
  orbRecK_sound dFacts.2.2.2

theorem dAct_tkey {j : ℕ} (hj : j < 5) (u : Fin 7 → Fin 276) :
    dActB j (tkey 9 u) = tkey 9 (fun i => dv j (u i)) :=
  mapKey_tkey (by norm_num) (prepD hj) u

theorem reachD : ∀ e, ActReach dActB 5 (subKey 9 KPB 0 7) e →
    ∃ r ∈ DB, e = tkey 9 (fun i => r (vD i)) := by
  intro e he
  induction he with
  | root =>
    refine ⟨1, one_mem _, ?_⟩
    rw [subKey_tkey hvD]
    rfl
  | @step e j _ hj ih =>
    obtain ⟨r, hr, rfl⟩ := ih
    refine ⟨dv j * r, mul_mem (dv_mem_DB hj) hr, ?_⟩
    rw [dAct_tkey hj]
    rfl

@[expose] noncomputable def ED : Finset (Fin 7 → Fin 276) :=
  Finset.univ.filter fun u => tkey 9 u ∈ DK

theorem mem_ED {u : Fin 7 → Fin 276} : u ∈ ED ↔ tkey 9 u ∈ DK := by
  simp [ED]

theorem card_ED : ED.card = 243 := by
  have himg : ED.image (tkey 9) = DK.toFinset := by
    ext k
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_ED.1 hu
    · intro hk
      obtain ⟨r, -, rfl⟩ := reachD k (recD.2.2.2.2 k hk)
      exact ⟨_, mem_ED.2 hk, rfl⟩
  rw [← Finset.card_image_of_injective _ (fun u u' h => tkey_inj (w := 9) (by norm_num) h), himg,
    List.toFinset_card_of_nodup (List.Nodup.of_map _ recD.2.1), recD.1]

theorem prodKB6 : ∏ t ∈ Finset.Ico 6 17, getS KB t = 3 := by decide +kernel

theorem fixD_eq_one :
    ∀ g ∈ co3P, (∀ i, g (vD i) = vD i) → g = 1 := by
  intro g hg hv
  have hc := chainB 6 (by norm_num)
  rw [prodKB6] at hc
  set G6 := stabB co3P bB 6
  have hG6 : Nat.card G6 = 3 := by rw [← hc.1]; exact hc.2
  have hgG : g ∈ G6 := ⟨hg, fun t ht => by rw [← vD_lt ht]; exact hv _⟩
  have hxG : xB ∈ G6 := ⟨xB_mem, fun t ht => fixB_lt (by omega)⟩
  set H := stabB G6 (fun _ => bB 15) 1
  have hHG : H ≤ G6 := fun h hh => hh.1
  have hgH : g ∈ H := ⟨hgG, fun _ _ => by rw [← vD6]; exact hv 6⟩
  have hxH : xB ∉ H := fun h => xB_b15 (h.2 0 (by norm_num))
  have hdvd : Nat.card H ∣ 3 := hG6 ▸ Subgroup.card_dvd_of_le hHG
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · rw [Subgroup.eq_bot_of_card_eq H h1] at hgH
    exact (mem_bot).1 hgH
  · exfalso
    have : H = G6 := Subgroup.eq_of_le_of_card_ge hHG (by rw [hG6, h3])
    exact hxH (this ▸ hxG)

theorem keyD_facts :
    Nat.card DB = ED.card ∧ ∀ y ∈ co3P, (fun i => y (vD i)) ∈ ED → y ∈ DB :=
  key_orbit DB_eq (DB_le.trans inf_le_right) vD fixD_eq_one ED
    (mem_ED.2 (by rw [← subKey_tkey hvD]; exact recD.2.2.1 (by norm_num)))
    (by
      rintro e he _ ⟨j, rfl⟩
      have h := recD.2.2.2.1 _ (mem_ED.1 he) j j.2
      rw [dAct_tkey j.2] at h
      exact mem_ED.2 h)
    (by
      intro e he
      obtain ⟨r, hr, he'⟩ := reachD _ (recD.2.2.2.2 _ (mem_ED.1 he))
      exact ⟨r, hr, (tkey_inj (w := 9) (by norm_num) he').symm⟩)

theorem card_DB :
    Nat.card DB = 243 := by
  rw [keyD_facts.1, card_ED]

theorem conj_mem_DB
    {yp : ℕ} {y : Equiv.Perm (Fin 276)} (hy : PRep 276 9 yp y)
    (hn : normK 276 9 511 DGp 5 yp KPB 0 7 DK = true) {j : ℕ} (hj : j < 5)
    (hP : y * dv j * y⁻¹ ∈ co3P) : y * dv j * y⁻¹ ∈ DB := by
  obtain ⟨hp, hk⟩ := normK_sound hn
  have hyi := prep_inv hp hy
  have e := conjKey_tkey hy hyi (prepD hj) hvD
  refine keyD_facts.2 _ hP (mem_ED.2 ?_)
  rw [← e]
  exact hk j hj

end CertificateChecks.KernelCo3Cent

end
