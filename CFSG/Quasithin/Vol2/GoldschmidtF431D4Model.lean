module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Gen
public import Certificates.Certificate4234

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

abbrev D : Type := ↥trialityGroup8

@[expose, irreducible] def cz : ClassData := mkClass d4Gens z0R

theorem cz_eq : cz = mkClass d4Gens z0R := by
  unfold cz
  rfl

theorem d4Gens_size' : d4Gens.size = 8 := rfl

section Link

theorem link_parts : gensOK d4Gens = true ∧
    classTreeOK d4Gens z0R cz.T cz.P cz.K cz.idx = true ∧ cz.T.size = 819 ∧
    ∀ j < 8, ∀ i < 819, (permArrs[j]!)[i]! < 819 ∧
      cz.T[(permArrs[j]!)[i]!]! = conjR d4Gens[j]! cz.T[i]! := by
  have h := Certificates.certificate4234
  simp only [CFSG.D4Hex.linkCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h, -⟩, -⟩ := h
  simp only [linkCheckOn, Bool.and_eq_true, beq_iff_eq] at h
  rw [cz_eq]
  obtain ⟨⟨⟨⟨hg, hc⟩, hs⟩, -⟩, hp⟩ := h
  refine ⟨hg, hc, hs, fun j hj i hi => ?_⟩
  have := allLt_spec (allLt_spec hp hj) hi
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem lineCheck_true : lineCheck = true := by
  have h := Certificates.certificate4234
  simp only [CFSG.D4Hex.linkCheck, Bool.and_eq_true] at h
  exact h.1.2

theorem baseFlagCheck_true : baseFlagCheck = true := by
  have h := Certificates.certificate4234
  simp only [CFSG.D4Hex.linkCheck, Bool.and_eq_true] at h
  exact h.2

theorem gens_hyp : ∀ k < d4Gens.size, RepE d4E d4Gens[k]! (d4GenG k) ∧
    d4GenG k * d4GenG k = 1 :=
  mul_self_of_gensOK (fun _ hk => repE_d4Gens (by rw [d4Gens_size'] at hk; exact hk))
    link_parts.1

theorem lt_size_cz {i : ℕ} (hi : i < 819) : i < cz.T.size := by
  rw [link_parts.2.2.1]
  exact hi

theorem exists_conj_cz : ∀ i < cz.T.size, ∃ c : D, RepE d4E cz.T[i]! (c * d4z * c⁻¹) :=
  exists_conj_of_classTreeOK gens_hyp repE_z0R link_parts.2.1

theorem validR_cz {i : ℕ} (hi : i < 819) : validR cz.T[i]! = true :=
  ((classTreeOK_parts link_parts.2.1).2.2 i (lt_size_cz hi)).1

theorem idx_cz {i : ℕ} (hi : i < 819) : cz.idx cz.T[i]! = i :=
  ((classTreeOK_parts link_parts.2.1).2.2 i (lt_size_cz hi)).2.1

@[expose] noncomputable def zElt (i : Fin 819) : D :=
  Classical.choose (exists_conj_cz i.1 (lt_size_cz i.2)) * d4z *
    (Classical.choose (exists_conj_cz i.1 (lt_size_cz i.2)))⁻¹

theorem repE_zElt (i : Fin 819) : RepE d4E cz.T[i.1]! (zElt i) :=
  Classical.choose_spec (exists_conj_cz i.1 (lt_size_cz i.2))

theorem zElt_zero : zElt ⟨0, by norm_num⟩ = d4z := by
  have h0 : cz.T[0]! = z0R := (classTreeOK_parts link_parts.2.1).2.1
  have := repE_zElt ⟨0, by norm_num⟩
  rw [show ((⟨0, by norm_num⟩ : Fin 819) : ℕ) = 0 from rfl, h0] at this
  exact eq_of_repE d4E_injective this repE_z0R

theorem zElt_injective : Function.Injective zElt := by
  intro i j h
  have hi := repE_zElt i
  have hj := repE_zElt j
  rw [h] at hi
  have := arr_eq_of_repE (validR_cz i.2) (validR_cz j.2) hi hj
  apply Fin.ext
  rw [← idx_cz i.2, ← idx_cz j.2, this]

theorem gen_conj {j : ℕ} (hj : j < 8) (i : Fin 819) :
    d4GenG j * zElt i * (d4GenG j)⁻¹ =
      zElt ⟨(permArrs[j]!)[i.1]!, (link_parts.2.2.2 j hj i.1 i.2).1⟩ := by
  have hg := gens_hyp j (by rw [d4Gens_size']; exact hj)
  have h1 := repE_conjR hg.1 (repE_zElt i) hg.2
  have h2 := (link_parts.2.2.2 j hj i.1 i.2).2
  have h3 := repE_zElt ⟨(permArrs[j]!)[i.1]!, (link_parts.2.2.2 j hj i.1 i.2).1⟩
  have h4 : RepE d4E cz.T[(permArrs[j]!)[i.1]!]! (d4GenG j * zElt i * (d4GenG j)⁻¹) := by
    rw [h2]
    exact h1
  exact eq_of_repE d4E_injective h4 h3

theorem d4GenG_lt_eight (k : ℕ) : ∃ j < 8, d4GenG k = d4GenG j := by
  by_cases hk : k < 8
  · exact ⟨k, hk, rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 8 := ⟨k - 8, by omega⟩
    exact ⟨7, by norm_num, rfl⟩

theorem exists_conj_zElt (g : D) : ∀ i : Fin 819, ∃ i' : Fin 819, g * zElt i * g⁻¹ = zElt i' := by
  have hg : g ∈ Subgroup.closure (Set.range d4GenG) := by
    rw [closure_d4GenG]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨j, hj, hk⟩ := d4GenG_lt_eight k
    rw [hk]
    exact fun i => ⟨_, gen_conj hj i⟩
  | one => exact fun i => ⟨i, by simp⟩
  | mul x y _ _ ihx ihy =>
    intro i
    obtain ⟨i1, h1⟩ := ihy i
    obtain ⟨i2, h2⟩ := ihx i1
    refine ⟨i2, ?_⟩
    calc x * y * zElt i * (x * y)⁻¹ = x * (y * zElt i * y⁻¹) * x⁻¹ := by group
      _ = zElt i2 := by rw [h1, h2]
  | inv x _ ihx =>
    choose f hf using ihx
    have hinj : Function.Injective f := by
      intro i j hij
      apply zElt_injective
      have := hf i
      rw [hij, ← hf j] at this
      simpa using this
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro i
    obtain ⟨i', hi'⟩ := hsurj i
    refine ⟨i', ?_⟩
    have h := hf i'
    rw [hi'] at h
    rw [← h]
    group

@[expose] noncomputable def actFun (g : D) (i : Fin 819) : Fin 819 :=
  Classical.choose (exists_conj_zElt g i)

theorem zElt_actFun (g : D) (i : Fin 819) : zElt (actFun g i) = g * zElt i * g⁻¹ :=
  (Classical.choose_spec (exists_conj_zElt g i)).symm

theorem actFun_mul (g h : D) (i : Fin 819) : actFun (g * h) i = actFun g (actFun h i) := by
  apply zElt_injective
  rw [zElt_actFun, zElt_actFun, zElt_actFun]
  group

theorem actFun_one (i : Fin 819) : actFun 1 i = i := by
  apply zElt_injective
  rw [zElt_actFun]
  simp

@[expose] noncomputable def act : D →* Equiv.Perm (Fin 819) where
  toFun g :=
    { toFun := actFun g
      invFun := actFun g⁻¹
      left_inv := fun i => by rw [← actFun_mul, inv_mul_cancel, actFun_one]
      right_inv := fun i => by rw [← actFun_mul, mul_inv_cancel, actFun_one] }
  map_one' := Equiv.ext actFun_one
  map_mul' g h := Equiv.ext (actFun_mul g h)

theorem zElt_act (g : D) (i : Fin 819) : zElt (act g i) = g * zElt i * g⁻¹ :=
  zElt_actFun g i

theorem act_gen {j : ℕ} (hj : j < 8) : Rep 819 permArrs[j]! (act (d4GenG j)) := by
  intro x
  have h := gen_conj hj x
  rw [← zElt_act] at h
  exact congrArg Fin.val (zElt_injective h).symm

@[expose] def d4WordArr (w : List ℕ) : Array ℕ :=
  w.foldr (fun k acc => compA 819 permArrs[k]! acc) (idA 819)

theorem rep_d4WordArr : ∀ w : List ℕ, (∀ k ∈ w, k < 8) →
    Rep 819 (d4WordArr w) (act (d4Word w))
  | [], _ => by
    have := rep_idA (n := 819)
    simpa [d4WordArr, d4Word] using this
  | k :: w, hw => by
    have h1 := act_gen (hw k List.mem_cons_self)
    have h2 := rep_d4WordArr w (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))
    have h3 := rep_compA h1 h2
    simpa [d4WordArr, d4Word, map_mul] using h3

noncomputable instance instMulActionPt : MulAction D (Fin 819) := MulAction.compHom _ act

theorem smul_pt_def (g : D) (i : Fin 819) : g • i = act g i := rfl

abbrev pt0 : Fin 819 := ⟨0, by norm_num⟩

theorem smul_pt0_iff (g : D) : g • pt0 = pt0 ↔ g * d4z = d4z * g := by
  rw [smul_pt_def]
  constructor
  · intro h
    have := zElt_act g pt0
    rw [h, zElt_zero] at this
    calc g * d4z = (g * d4z * g⁻¹) * g := by group
      _ = d4z * g := by rw [← this]
  · intro h
    apply zElt_injective
    rw [zElt_act, zElt_zero]
    calc g * d4z * g⁻¹ = d4z * g * g⁻¹ := by rw [h]
      _ = d4z := by group

end Link

end CFSG.Quasithin.D4Hex
