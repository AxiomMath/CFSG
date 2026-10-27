module

public import CFSG.Sporadic.Schreier.ONLocalOrders
public import CFSG.Sporadic.Schreier.ONEightNormalizersCheck
public import CFSG.CGT.Stroth77.Section43CoreIII
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate13790

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native Subgroup

theorem e8n_cert :
    onTArrs.size = 6 ∧ allBelowN 6 (fun h => pisInv nPts onTArrs[h]! onTInvArrs[h]!) = true ∧
      onNormArrs.size = 4 ∧
      allBelowN 4 (fun i => pisInv nPts onNormArrs[i]! onNormInvArrs[i]!) = true ∧
      pe8OK (onE8Arr 0 0) (onE8Arr 0 1) (onE8Arr 0 2) = true ∧
      pe8OK (onE8Arr 1 0) (onE8Arr 1 1) (onE8Arr 1 2) = true ∧
      allBelowN 4 (fun i => pnormOK onNormArrs[i]! onNormInvArrs[i]!
        (onE8Arr onNormTags[i]! 0) (onE8Arr onNormTags[i]! 1) (onE8Arr onNormTags[i]! 2)) = true ∧
      peq nPts (pword nPts onNormArrs onNormInvArrs onAWord) (wordArr [1]) = true ∧
      peq nPts (pword nPts onNormArrs onNormInvArrs onBWord) (wordArr [2]) = true := by
  have h := Certificates.certificate13790
  simp only [onEightNormalizersCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

@[expose] def onTg (h : ℕ) :
    Equiv.Perm (Fin N) :=
  onTgens.getD h 1

theorem onTg_eq {h : ℕ}
    (hh : h < 6) : onTg h = onTgens[h]'(by rw [onTgens_length]; exact hh) := by
  rw [onTg, List.getD_eq_getElem]

theorem onTg_mem {h : ℕ}
    (hh : h < 6) : onTg h ∈ onT := by
  rw [onTg_eq hh]
  exact subset_closure (List.getElem_mem _)

theorem prep_onTArrs
    {h : ℕ} (hh : h < 6) : PRep N onTArrs[h]! (onTg h) := by
  have hl : h < (evalList Data.TWords).length := by
    have := onTgens_length
    rw [onTgens] at this
    rw [this]
    exact hh
  rw [onTArrs, onTg_eq hh]
  exact prep_wordArrs words_ok.1 h hl

theorem prep_onTInvArrs
    {h : ℕ} (hh : h < 6) :
    PRep N onTInvArrs[h]! (onTg h)⁻¹ :=
  prep_inv_of_pisInv (prep_onTArrs hh) (allBelowN_spec e8n_cert.2.1 hh)

@[expose] def onE8 (j k : ℕ) :
    Equiv.Perm (Fin N) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 6 => onTg h) (ptoLetters 6 (onE8Words[j]!)[k]!)

@[expose] def onE8Grp (j : ℕ) :
    Subgroup (Equiv.Perm (Fin N)) :=
  closure {onE8 j 0, onE8 j 1, onE8 j 2}

theorem onE8Words_ok : ∀ j < 2, ∀ k < 3, plettersOK 6 (onE8Words[j]!)[k]! = true := by
  decide

theorem prep_onE8
    {j k : ℕ} (hj : j < 2)
    (hk : k < 3) : PRep N (onE8Arr j k) (onE8 j k) :=
  prep_pword (gs := onTg) (fun _ hh => prep_onTArrs hh) (fun _ hh => prep_onTInvArrs hh) _
    (onE8Words_ok j hj k hk)

theorem onE8_mem (j k : ℕ) :
    onE8 j k ∈ onT := by
  refine (closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact onTg_mem h.2

theorem onE8Grp_le (j : ℕ) :
    onE8Grp j ≤ onT := by
  rw [onE8Grp, closure_le]
  rintro _ (rfl | rfl | rfl) <;> exact onE8_mem _ _

theorem facts_of_pe8OK {x y z : Equiv.Perm (Fin N)} {ax ay az : Array ℕ} (hx : PRep N ax x)
    (hy : PRep N ay y) (hz : PRep N az z) (h : pe8OK ax ay az = true) :
    x * x = 1 ∧ y * y = 1 ∧ z * z = 1 ∧ x * y = y * x ∧ x * z = z * x ∧ y * z = z * y ∧
      x ≠ 1 ∧ y ≠ 1 ∧ y ≠ x ∧ z ≠ 1 ∧ z ≠ x ∧ z ≠ y ∧ z ≠ x * y := by
  simp only [pe8OK, pinvol, pcommute, pelems4, Bool.and_eq_true, Bool.not_eq_true',
    List.all_cons, List.all_nil, Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxx, hyy⟩, hzz⟩, hxy⟩, hxz⟩, hyz⟩, hx1⟩, hy1⟩, hyx⟩, hz1, hzx, hzy, hzxy⟩ := h
  have ne : ∀ {a : Array ℕ} {u : Array ℕ} {g h : Equiv.Perm (Fin N)}, PRep N a g →
      PRep N u h → peq nPts a u = false → g ≠ h := fun ha hu hf he => by
    have := (peq_iff ha hu).2 he
    rw [hf] at this
    exact Bool.false_ne_true this
  exact ⟨eq_of_peq (prep_pcomp hx hx) prep_pid hxx, eq_of_peq (prep_pcomp hy hy) prep_pid hyy,
    eq_of_peq (prep_pcomp hz hz) prep_pid hzz,
    eq_of_peq (prep_pcomp hx hy) (prep_pcomp hy hx) hxy,
    eq_of_peq (prep_pcomp hx hz) (prep_pcomp hz hx) hxz,
    eq_of_peq (prep_pcomp hy hz) (prep_pcomp hz hy) hyz, ne hx prep_pid hx1, ne hy prep_pid hy1,
    ne hy hx hyx, ne hz prep_pid hz1, ne hz hx hzx, ne hz hy hzy, ne hz (prep_pcomp hx hy) hzxy⟩

theorem elem_eight_of_three {G : Type*} [Group G] {x y z : G} (hxx : x * x = 1)
    (hyy : y * y = 1) (hzz : z * z = 1) (hxy : x * y = y * x) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) (hz1 : z ≠ 1)
    (hzx : z ≠ x) (hzy : z ≠ y) (hzxy : z ≠ x * y) :
    (∀ a ∈ closure ({x, y, z} : Set G), ∀ b ∈ closure ({x, y, z} : Set G), a * b = b * a) ∧
      (∀ a ∈ closure ({x, y, z} : Set G), a * a = 1) ∧
      Nat.card (closure ({x, y, z} : Set G)) = 8 := by
  have hxyxy : x * y * (x * y) = 1 := by
    rw [mul_assoc, ← mul_assoc y x y, ← hxy, mul_assoc, hyy, mul_one, hxx]
  have hind : ∀ a b c : Bool, CGT.Stroth77.Stroth42Core.bpow x a *
      CGT.Stroth77.Stroth42Core.bpow y b * CGT.Stroth77.Stroth42Core.bpow z c = 1 →
        a = false ∧ b = false ∧ c = false := by
    intro a b c habc
    cases a <;> cases b <;> cases c <;>
      simp only [CGT.Stroth77.Stroth42Core.bpow, Bool.false_eq_true, if_false, if_true,
        one_mul, mul_one] at habc ⊢
    · exact ⟨trivial, trivial, trivial⟩
    · exact absurd habc hz1
    · exact absurd habc hy1
    · exact absurd (mul_left_cancel (habc.trans hyy.symm)) hzy
    · exact absurd habc hx1
    · exact absurd (mul_left_cancel (habc.trans hxx.symm)) hzx
    · exact absurd (mul_left_cancel (habc.trans hxx.symm)) hyx
    · exact absurd (mul_left_cancel (habc.trans hxyxy.symm)) hzxy
  obtain ⟨hsq, hcard⟩ := CGT.Stroth77.Stroth43Core.closure_three_inv hxx hyy hzz hxy hxz hyz hind
  refine ⟨fun a ha b hb => ?_, hsq, hcard⟩
  have hab := hsq (a * b) (mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, ha', hb']

theorem onE8Grp_facts
    {j : ℕ} (hj : j < 2) :
    (∀ a ∈ onE8Grp j, ∀ b ∈ onE8Grp j, a * b = b * a) ∧ (∀ a ∈ onE8Grp j, a * a = 1) ∧
      Nat.card (onE8Grp j) = 8 := by
  have hcheck : pe8OK (onE8Arr j 0) (onE8Arr j 1) (onE8Arr j 2) = true := by
    interval_cases j
    · exact e8n_cert.2.2.2.2.1
    · exact e8n_cert.2.2.2.2.2.1
  obtain ⟨hxx, hyy, hzz, hxy, hxz, hyz, hx1, hy1, hyx, hz1, hzx, hzy, hzxy⟩ :=
    facts_of_pe8OK (prep_onE8 hj (by norm_num)) (prep_onE8 hj (by norm_num))
      (prep_onE8 hj (by norm_num)) hcheck
  exact elem_eight_of_three hxx hyy hzz hxy hxz hyz hx1 hy1 hyx hz1 hzx hzy hzxy

theorem pelems8_rep {x y z : Equiv.Perm (Fin N)} {ax ay az : Array ℕ} (hx : PRep N ax x)
    (hy : PRep N ay y) (hz : PRep N az z) :
    ∀ f ∈ pelems8 ax ay az, ∃ g ∈ closure ({x, y, z} : Set (Equiv.Perm (Fin N))), PRep N f g := by
  have hxS : x ∈ closure ({x, y, z} : Set (Equiv.Perm (Fin N))) := subset_closure (by simp)
  have hyS : y ∈ closure ({x, y, z} : Set (Equiv.Perm (Fin N))) := subset_closure (by simp)
  have hzS : z ∈ closure ({x, y, z} : Set (Equiv.Perm (Fin N))) := subset_closure (by simp)
  intro f hf
  simp only [pelems8, pelems4, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h | h | h
  · exact ⟨1, one_mem _, h ▸ prep_pid⟩
  · exact ⟨x, hxS, h ▸ hx⟩
  · exact ⟨y, hyS, h ▸ hy⟩
  · exact ⟨x * y, mul_mem hxS hyS, h ▸ prep_pcomp hx hy⟩
  · exact ⟨1 * z, mul_mem (one_mem _) hzS, h ▸ prep_pcomp prep_pid hz⟩
  · exact ⟨x * z, mul_mem hxS hzS, h ▸ prep_pcomp hx hz⟩
  · exact ⟨y * z, mul_mem hyS hzS, h ▸ prep_pcomp hy hz⟩
  · exact ⟨x * y * z, mul_mem (mul_mem hxS hyS) hzS, h ▸ prep_pcomp (prep_pcomp hx hy) hz⟩

theorem mem_normalizer_of_pnormOK {n x y z : Equiv.Perm (Fin N)} {an ani ax ay az : Array ℕ}
    (hn : PRep N an n) (hni : PRep N ani n⁻¹) (hx : PRep N ax x) (hy : PRep N ay y)
    (hz : PRep N az z) (h : pnormOK an ani ax ay az = true) :
    n ∈ normalizer ((closure ({x, y, z} : Set (Equiv.Perm (Fin N)))) : Set (Equiv.Perm (Fin N))) := by
  set S : Set (Equiv.Perm (Fin N)) := {x, y, z} with hSdef
  have hconj : ∀ {e : Equiv.Perm (Fin N)} {ae : Array ℕ}, PRep N ae e →
      (pelems8 ax ay az).any (fun f => peq nPts (pcomp nPts (pcomp nPts an ae) ani) f) = true →
        n * e * n⁻¹ ∈ closure S := fun he hany => by
    obtain ⟨f, hf, hpf⟩ := List.any_eq_true.1 hany
    obtain ⟨g, hg, hfg⟩ := pelems8_rep hx hy hz f hf
    rw [eq_of_peq (prep_pcomp (prep_pcomp hn he) hni) hfg hpf]
    exact hg
  simp only [pnormOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hgen : ∀ e ∈ S, n * e * n⁻¹ ∈ closure S := by
    rintro e (rfl | rfl | rfl)
    · exact hconj hx h1
    · exact hconj hy h2
    · exact hconj hz h3
  have hmap : (closure S).map (MulAut.conj n).toMonoidHom ≤ closure S := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact hgen e he
  refine Subgroup.mem_normalizer_fintype fun g hg => hmap ⟨g, hg, ?_⟩
  simp [MulAut.conj_apply]

@[expose] def onNorm (i : ℕ) :
    Equiv.Perm (Fin N) :=
  evalS onNormWords[i]!

theorem onNormWords_ok : ∀ i < 4, plettersOK 7 onNormWords[i]! = true := by
  decide

theorem prep_onNormArrs
    {i : ℕ} (hi : i < 4) : PRep N onNormArrs[i]! (onNorm i) := by
  rw [onNormArrs, getElem!_map' _ _ (show i < onNormWords.size from hi)]
  exact prep_wordArr (onNormWords_ok i hi)

theorem prep_onNormInvArrs
    {i : ℕ} (hi : i < 4) :
    PRep N onNormInvArrs[i]! (onNorm i)⁻¹ :=
  prep_inv_of_pisInv (prep_onNormArrs hi) (allBelowN_spec e8n_cert.2.2.2.1 hi)

theorem onNorm_mem_normalizer
    {i : ℕ} (hi : i < 4) :
    onNorm i ∈ normalizer (onE8Grp onNormTags[i]! : Set (Equiv.Perm (Fin N))) := by
  have htag : onNormTags[i]! < 2 := by interval_cases i <;> decide
  exact mem_normalizer_of_pnormOK (prep_onNormArrs hi) (prep_onNormInvArrs hi)
    (prep_onE8 htag (by norm_num)) (prep_onE8 htag (by norm_num)) (prep_onE8 htag (by norm_num))
    (allBelowN_spec e8n_cert.2.2.2.2.2.2.1 hi)

theorem evalS_one :
    evalS [1] = a0 := by
  have h : ptoLetters 7 [1] = [(⟨0, by omega⟩, true)] := by decide
  rw [evalS, h, Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_nil,
    mul_one]
  exact cert_on_schreier_action_data.2.2.2.2.2.1

theorem evalS_two :
    evalS [2] = a1 := by
  have h : ptoLetters 7 [2] = [(⟨1, by omega⟩, true)] := by decide
  rw [evalS, h, Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_nil,
    mul_one]
  exact cert_on_schreier_action_data.2.2.2.2.2.2.1

theorem onNorm_word_eq
    {w v : List ℤ}
    (hw : plettersOK 4 w = true) (hv : plettersOK 7 v = true)
    (h : peq nPts (pword nPts onNormArrs onNormInvArrs w) (wordArr v) = true) :
    Quiver.SchreierGraph.evalWord (fun i : Fin 4 => onNorm i) (ptoLetters 4 w) = evalS v :=
  eq_of_peq (prep_pword (gs := onNorm) (fun _ hi => prep_onNormArrs hi)
    (fun _ hi => prep_onNormInvArrs hi) w hw) (prep_wordArr hv) h

theorem Pv_le_closure_onNorm :
    Pv ≤ closure (Set.range fun i : Fin 4 => onNorm i) := by
  rw [Pv, closure_le]
  rintro g (rfl | rfl)
  · rw [← evalS_one, ← onNorm_word_eq (by decide) (by decide) e8n_cert.2.2.2.2.2.2.2.1]
    exact Quiver.SchreierGraph.evalWord_mem_closure _ _
  · rw [← evalS_two, ← onNorm_word_eq (by decide) (by decide) e8n_cert.2.2.2.2.2.2.2.2]
    exact Quiver.SchreierGraph.evalWord_mem_closure _ _

theorem on_eight_normalizers_Pv :
    ∃ E₀ E₁ : Subgroup (Equiv.Perm (Fin N)), E₀ ≤ onT ∧ E₁ ≤ onT ∧
      (∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) ∧ (∀ x ∈ E₀, x * x = 1) ∧ Nat.card E₀ = 8 ∧
      (∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x) ∧ (∀ x ∈ E₁, x * x = 1) ∧ Nat.card E₁ = 8 ∧
      Pv ≤ Pv ⊓ normalizer (E₀ : Set (Equiv.Perm (Fin N))) ⊔
        Pv ⊓ normalizer (E₁ : Set (Equiv.Perm (Fin N))) := by
  obtain ⟨hc₀, hs₀, h8₀⟩ := onE8Grp_facts (j := 0) (by norm_num)
  obtain ⟨hc₁, hs₁, h8₁⟩ := onE8Grp_facts (j := 1) (by norm_num)
  refine ⟨onE8Grp 0, onE8Grp 1, onE8Grp_le 0, onE8Grp_le 1, hc₀, hs₀, h8₀, hc₁, hs₁, h8₁,
    Pv_le_closure_onNorm.trans ?_⟩
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  have hmem := onNorm_mem_normalizer i.2
  have htag : onNormTags[(i : ℕ)]! = 0 ∨ onNormTags[(i : ℕ)]! = 1 := by
    fin_cases i <;> decide
  rcases htag with h | h
  · rw [h] at hmem
    exact mem_sup_left ⟨evalS_mem _, hmem⟩
  · rw [h] at hmem
    exact mem_sup_right ⟨evalS_mem _, hmem⟩

theorem normalizer_subgroupOf_sup_eq_top {X : Type*} [Group X] {P E₀ E₁ : Subgroup X}
    (hE₀ : E₀ ≤ P) (hE₁ : E₁ ≤ P)
    (hgen : P ≤ P ⊓ normalizer (E₀ : Set X) ⊔ P ⊓ normalizer (E₁ : Set X)) :
    normalizer ((E₀.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊔
      normalizer ((E₁.subgroupOf P : Subgroup ↥P) : Set ↥P) = ⊤ := by
  let K₀ : Subgroup ↥P := normalizer ((E₀.subgroupOf P : Subgroup ↥P) : Set ↥P)
  let K₁ : Subgroup ↥P := normalizer ((E₁.subgroupOf P : Subgroup ↥P) : Set ↥P)
  have hmap₀ : P ⊓ normalizer (E₀ : Set X) ≤ K₀.map P.subtype := by
    intro g hg
    refine Subgroup.mem_map_of_mem P.subtype (K := K₀) (x := ⟨g, hg.1⟩) ?_
    change (⟨g, hg.1⟩ : ↥P) ∈
      normalizer ((E₀.subgroupOf P : Subgroup ↥P) : Set ↥P)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_set_normalizer_iff.mp hg.2 (h : X))
  have hmap₁ : P ⊓ normalizer (E₁ : Set X) ≤ K₁.map P.subtype := by
    intro g hg
    refine Subgroup.mem_map_of_mem P.subtype (K := K₁) (x := ⟨g, hg.1⟩) ?_
    change (⟨g, hg.1⟩ : ↥P) ∈
      normalizer ((E₁.subgroupOf P : Subgroup ↥P) : Set ↥P)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_set_normalizer_iff.mp hg.2 (h : X))
  have hle : P ⊓ normalizer (E₀ : Set X) ⊔ P ⊓ normalizer (E₁ : Set X) ≤
      (K₀ ⊔ K₁).map P.subtype := by
    rw [Subgroup.map_sup]
    exact sup_le (hmap₀.trans le_sup_left) (hmap₁.trans le_sup_right)
  have htop : P ≤ (K₀ ⊔ K₁).map P.subtype := hgen.trans hle
  rw [eq_top_iff]
  intro p _
  obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp (htop p.2)
  have hkp' : k = p := Subtype.ext hkp
  rwa [hkp'] at hk

theorem exists_eight_normalizers_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (φ : X ≃* Y) (T : Sylow 2 X) {E₀ E₁ : Subgroup X} (hE₀ : E₀ ≤ T) (hE₁ : E₁ ≤ T)
    (hc₀ : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hs₀ : ∀ x ∈ E₀, x * x = 1)
    (h8₀ : Nat.card E₀ = 8)
    (hc₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x) (hs₁ : ∀ x ∈ E₁, x * x = 1)
    (h8₁ : Nat.card E₁ = 8)
    (hgen : normalizer (E₀ : Set X) ⊔ normalizer (E₁ : Set X) = ⊤) (R : Sylow 2 Y) :
    ∃ F₀ F₁ : Subgroup Y, F₀ ≤ R ∧ F₁ ≤ R ∧
      (∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x) ∧ (∀ x ∈ F₀, x * x = 1) ∧ Nat.card F₀ = 8 ∧
      (∀ x ∈ F₁, ∀ y ∈ F₁, x * y = y * x) ∧ (∀ x ∈ F₁, x * x = 1) ∧ Nat.card F₁ = 8 ∧
      normalizer (F₀ : Set Y) ⊔ normalizer (F₁ : Set Y) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_equiv X φ.toEquiv
  haveI : Finite (Sylow 2 Y) :=
    Finite.of_injective (fun S : Sylow 2 Y => (S : Set Y)) SetLike.coe_injective
  let T' : Sylow 2 Y := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective T
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y T' R
  let ψ : X ≃* Y := φ.trans (MulAut.conj g)
  have hR : (R : Subgroup Y) = (T' : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun S : Sylow 2 Y => (S : Subgroup Y)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    convert h.symm using 2
    ext x
    rfl
  have hψT : (T : Subgroup X).map ψ.toMonoidHom = (R : Subgroup Y) := by
    change (T : Subgroup X).map (φ.trans (MulAut.conj g)).toMonoidHom = (R : Subgroup Y)
    rw [hR, Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective T, Subgroup.map_map]
    rfl
  refine ⟨E₀.map ψ.toMonoidHom, E₁.map ψ.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hE₀).trans (le_of_eq hψT)
  · exact (Subgroup.map_mono hE₁).trans (le_of_eq hψT)
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hc₀ a ha b hb]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, hs₀ a ha, map_one]
  · exact (Subgroup.card_map_of_injective ψ.injective).trans h8₀
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hc₁ a ha b hb]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, hs₁ a ha, map_one]
  · exact (Subgroup.card_map_of_injective ψ.injective).trans h8₁
  · have h := congrArg (Subgroup.map ψ.toMonoidHom) hgen
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective] at h
    rwa [Subgroup.map_equiv_normalizer_eq E₀ ψ,
      Subgroup.map_equiv_normalizer_eq E₁ ψ] at h

theorem exists_eight_normalizers_of_le {X Y : Type*} [Group X] [Group Y] [Finite X]
    {P T E₀ E₁ : Subgroup X} (φ : ↥P ≃* Y) (S : Sylow 2 ↥P)
    (hS : (S : Subgroup ↥P) = T.subgroupOf P) (hTP : T ≤ P) (hE₀ : E₀ ≤ T) (hE₁ : E₁ ≤ T)
    (hc₀ : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hs₀ : ∀ x ∈ E₀, x * x = 1)
    (h8₀ : Nat.card E₀ = 8)
    (hc₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x) (hs₁ : ∀ x ∈ E₁, x * x = 1)
    (h8₁ : Nat.card E₁ = 8)
    (hgen : P ≤ P ⊓ normalizer (E₀ : Set X) ⊔ P ⊓ normalizer (E₁ : Set X)) (R : Sylow 2 Y) :
    ∃ F₀ F₁ : Subgroup Y, F₀ ≤ R ∧ F₁ ≤ R ∧
      (∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x) ∧ (∀ x ∈ F₀, x * x = 1) ∧ Nat.card F₀ = 8 ∧
      (∀ x ∈ F₁, ∀ y ∈ F₁, x * y = y * x) ∧ (∀ x ∈ F₁, x * x = 1) ∧ Nat.card F₁ = 8 ∧
      normalizer (F₀ : Set Y) ⊔ normalizer (F₁ : Set Y) = ⊤ := by
  have hE'₀ : E₀.subgroupOf P ≤ S := by
    rw [hS]
    exact Subgroup.subgroupOf_mono P hE₀
  have hE'₁ : E₁.subgroupOf P ≤ S := by
    rw [hS]
    exact Subgroup.subgroupOf_mono P hE₁
  have hc'₀ : ∀ x ∈ E₀.subgroupOf P, ∀ y ∈ E₀.subgroupOf P, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hc₀ x.1 (Subgroup.mem_subgroupOf.mp hx) y.1
      (Subgroup.mem_subgroupOf.mp hy))
  have hs'₀ : ∀ x ∈ E₀.subgroupOf P, x * x = 1 := by
    intro x hx
    exact Subtype.ext (hs₀ x.1 (Subgroup.mem_subgroupOf.mp hx))
  have h8'₀ : Nat.card (E₀.subgroupOf P) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE₀.trans hTP)).toEquiv, h8₀]
  have hc'₁ : ∀ x ∈ E₁.subgroupOf P, ∀ y ∈ E₁.subgroupOf P, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hc₁ x.1 (Subgroup.mem_subgroupOf.mp hx) y.1
      (Subgroup.mem_subgroupOf.mp hy))
  have hs'₁ : ∀ x ∈ E₁.subgroupOf P, x * x = 1 := by
    intro x hx
    exact Subtype.ext (hs₁ x.1 (Subgroup.mem_subgroupOf.mp hx))
  have h8'₁ : Nat.card (E₁.subgroupOf P) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE₁.trans hTP)).toEquiv, h8₁]
  have hgen' : normalizer ((E₀.subgroupOf P : Subgroup ↥P) : Set ↥P) ⊔
      normalizer ((E₁.subgroupOf P : Subgroup ↥P) : Set ↥P) = ⊤ :=
    normalizer_subgroupOf_sup_eq_top (hE₀.trans hTP) (hE₁.trans hTP) hgen
  exact exists_eight_normalizers_of_mulEquiv φ S hE'₀ hE'₁ hc'₀ hs'₀ h8'₀ hc'₁ hs'₁ h8'₁ hgen' R

theorem on_eight_normalizers
    {Y : Type} [Group Y]
    (hY : Blueprint.NativeSporadic.IsSporadic Y .ONan) (R : Sylow 2 Y) :
    ∃ F₀ F₁ : Subgroup Y, F₀ ≤ R ∧ F₁ ≤ R ∧
      (∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x) ∧ (∀ x ∈ F₀, x * x = 1) ∧ Nat.card F₀ = 8 ∧
      (∀ x ∈ F₁, ∀ y ∈ F₁, x * y = y * x) ∧ (∀ x ∈ F₁, x * x = 1) ∧ Nat.card F₁ = 8 ∧
      normalizer (F₀ : Set Y) ⊔ normalizer (F₁ : Set Y) = ⊤ := by
  obtain ⟨e⟩ : Nonempty (Y ≃* Blueprint.NativeSporadic.Carrier .ONan) := hY
  obtain ⟨E₀, E₁, hE₀, hE₁, hc₀, hs₀, h8₀, hc₁, hs₁, h8₁, hgen⟩ := on_eight_normalizers_Pv
  exact exists_eight_normalizers_of_le (onEquivPv.symm.trans e.symm) onTSylow onTSylow_coe
    onT_le hE₀ hE₁ hc₀ hs₀ h8₀ hc₁ hs₁ h8₁ hgen R

end CFSG.ONSchreier
