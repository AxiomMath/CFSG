module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModA
public import Certificates.Certificate7213
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Fischer

theorem pn_mem_iff : ∀ w < 64, pn w ∈ oPts ↔ ∃ p ∈ oPts, ∃ c < 4, c ≠ 0 ∧ w = sV c p := by
  decide +kernel

@[expose] def pnEqB (w w' : ℕ) : Bool :=
  w == 0 || w' == 0 || pn w != pn w' || (List.range 4).any fun c => c != 0 && w' == sV c w

theorem pnEqB_all : ∀ w < 64, ∀ w' < 64, pnEqB w w' = true := by decide +kernel

theorem pn_eq_imp {w w' : ℕ} (hw : w < 64) (hw' : w' < 64) (h0 : w ≠ 0) (h0' : w' ≠ 0)
    (he : pn w = pn w') : ∃ c < 4, c ≠ 0 ∧ w' = sV c w := by
  have h := pnEqB_all w hw w' hw'
  simp only [pnEqB, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true,
    List.mem_range, Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | ⟨c, hc, hc0, hce⟩
  · exact absurd h h0
  · exact absurd h h0'
  · exact absurd he h
  · exact ⟨c, hc, by simpa using hc0, by simpa using hce⟩

theorem oPts_lt : ∀ p ∈ oPts, p < 64 := by decide

theorem oPts_nodup : oPts.Nodup := by decide

theorem oPts_ne_zero : ∀ p ∈ oPts, p ≠ 0 := by decide

theorem oPts_eq_of_sV : ∀ p ∈ oPts, ∀ q ∈ oPts, ∀ c < 4, p = sV c q → p = q := by decide

theorem decF_ne_zero {c : ℕ} (hc : c < 4) (h0 : c ≠ 0) : decF c ≠ 0 := by
  intro h
  have := congrArg (fun x : F4 => x.code.val) h
  simp only [code_decF, Nat.mod_eq_of_lt hc] at this
  exact h0 this

theorem eq_decF (x : F4) : x = decF x.code.val := by
  apply f4_ext
  apply Fin.ext
  rw [code_decF, Nat.mod_eq_of_lt x.code.isLt]

theorem code_ne_zero {x : F4} (hx : x ≠ 0) : x.code.val ≠ 0 := by
  intro h
  apply hx
  apply f4_ext
  apply Fin.ext
  rw [h]
  rfl

theorem decV_injective {v w : ℕ} (hv : v < 64) (hw : w < 64) (h : decV v = decV w) : v = w := by
  rw [← encV_decV hv, ← encV_decV hw, h]

theorem decV_zero : decV 0 = 0 := by
  have h := decV_xor (v := 0) (w := 0) (by norm_num) (by norm_num)
  rw [show (0 : ℕ) ^^^ 0 = 0 from rfl] at h
  have h2 : decV 0 + 0 = decV 0 + decV 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem decV_ne_zero {v : ℕ} (hv : v < 64) (h0 : v ≠ 0) : decV v ≠ 0 := by
  intro h
  apply h0
  have : decV v = decV 0 := by rw [h, decV_zero]
  exact decV_injective hv (by norm_num) this

@[expose] def oVec : Set (Fin 3 → F4) := {x | ∃ p ∈ oPts, ∃ c : F4, c ≠ 0 ∧ x = c • decV p}

theorem mem_oVec_iff (x : Fin 3 → F4) : x ∈ oVec ↔ pn (encV x) ∈ oPts := by
  constructor
  · rintro ⟨p, hp, c, hc, rfl⟩
    have hpl := oPts_lt p hp
    have hcl := c.code.isLt
    rw [eq_decF c, ← decV_sV hcl hpl, encV_decV (sV_lt_64 _ hcl _ hpl)]
    exact (pn_mem_iff _ (sV_lt_64 _ hcl _ hpl)).2 ⟨p, hp, _, hcl, code_ne_zero hc, rfl⟩
  · intro h
    obtain ⟨p, hp, c, hcl, hc0, he⟩ := (pn_mem_iff _ (encV_lt x)).1 h
    refine ⟨p, hp, decF c, decF_ne_zero hcl hc0, ?_⟩
    rw [← decV_sV hcl (oPts_lt p hp), ← he, decV_encV]

theorem decV_mem_oVec {p : ℕ} (hp : p ∈ oPts) : decV p ∈ oVec :=
  ⟨p, hp, 1, one_ne_zero, (one_smul _ _).symm⟩

theorem smul_mem_oVec {c : F4} (hc : c ≠ 0) {x : Fin 3 → F4} (hx : x ∈ oVec) : c • x ∈ oVec := by
  obtain ⟨p, hp, d, hd, rfl⟩ := hx
  exact ⟨p, hp, c * d, mul_ne_zero hc hd, by rw [smul_smul]⟩

theorem oVec_finite : oVec.Finite := Set.toFinite _

theorem exists_mulVec_eq {g : Matrix.GeneralLinearGroup (Fin 3) F4}
    (hg : ∀ x ∈ oVec, (g : Matrix (Fin 3) (Fin 3) F4).mulVec x ∈ oVec) {y : Fin 3 → F4}
    (hy : y ∈ oVec) : ∃ x ∈ oVec, (g : Matrix (Fin 3) (Fin 3) F4).mulVec x = y := by
  have : Finite ↥oVec := oVec_finite.to_subtype
  let f : ↥oVec → ↥oVec := fun x => ⟨(g : Matrix (Fin 3) (Fin 3) F4).mulVec x, hg x x.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' := congrArg (fun z : ↥oVec => ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4).mulVec z) hab
    apply Subtype.ext
    simpa [f, Matrix.mulVec_mulVec] using hab'
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

@[expose] def gm : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4) where
  carrier := {g | ∀ x ∈ oVec, (g : Matrix (Fin 3) (Fin 3) F4).mulVec x ∈ oVec}
  mul_mem' := by
    intro g h hg hh x hx
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    exact hg _ (hh x hx)
  one_mem' := by
    intro x hx
    simpa using hx
  inv_mem' := by
    intro g hg y hy
    obtain ⟨x, hx, rfl⟩ := exists_mulVec_eq hg hy
    simpa [Matrix.mulVec_mulVec] using hx

theorem mem_gm {g : Matrix.GeneralLinearGroup (Fin 3) F4} :
    g ∈ gm ↔ ∀ x ∈ oVec, (g : Matrix (Fin 3) (Fin 3) F4).mulVec x ∈ oVec := Iff.rfl

theorem app_ofMat (M : Matrix (Fin 3) (Fin 3) F4) {v : ℕ} :
    M.mulVec (decV v) = decV ((Mc.ofMat M).app v) := by
  conv_lhs => rw [← Mc.toMat_ofMat M]
  exact Mc.toMat_mulVec _ (Mc.ofMat_valid M) v

theorem mem_gm_iff_inGm (g : Matrix.GeneralLinearGroup (Fin 3) F4) :
    g ∈ gm ↔ inGm (Mc.ofMat g) = true := by
  set M : Matrix (Fin 3) (Fin 3) F4 := (g : Matrix (Fin 3) (Fin 3) F4) with hM
  have hval := Mc.ofMat_valid M
  have hlt : ∀ v, (Mc.ofMat M).app v < 64 := fun v => Mc.app_lt _ hval
  constructor
  · intro hg
    have himg : ∀ p ∈ oPts, pn ((Mc.ofMat M).app p) ∈ oPts := by
      intro p hp
      have h1 := hg _ (decV_mem_oVec hp)
      rw [app_ofMat, mem_oVec_iff, encV_decV (hlt p)] at h1
      exact h1
    simp only [inGm, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq]
    refine ⟨himg, ?_⟩
    refine List.Nodup.map_on ?_ oPts_nodup
    intro p hp q hq hpq
    have hne : ∀ r ∈ oPts, (Mc.ofMat M).app r ≠ 0 := by
      intro r hr h0
      have h1 : M.mulVec (decV r) = 0 := by
        rw [app_ofMat, h0, decV_zero]
      have h2 := congrArg (fun z => ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4).mulVec z) h1
      simp only [hM, Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_inv,
        Matrix.mulVec_zero] at h2
      rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit),
        Matrix.one_mulVec] at h2
      exact decV_ne_zero (oPts_lt r hr) (oPts_ne_zero r hr) h2
    obtain ⟨c, hc, hc0, he⟩ := pn_eq_imp (hlt p) (hlt q) (hne p hp) (hne q hq) hpq
    have h1 : M.mulVec (decV q) = decF c • M.mulVec (decV p) := by
      rw [app_ofMat, app_ofMat, he, decV_sV hc (hlt p)]
    have h2 : M.mulVec (decV q) = M.mulVec (decF c • decV p) := by
      rw [h1, Matrix.mulVec_smul]
    have h3 := congrArg (fun z => ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4).mulVec z) h2
    simp only [hM, Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_inv] at h3
    rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit),
      Matrix.one_mulVec, Matrix.one_mulVec, ← decV_sV hc (oPts_lt p hp)] at h3
    have h4 := decV_injective (oPts_lt q hq) (sV_lt_64 _ hc _ (oPts_lt p hp)) h3
    exact (oPts_eq_of_sV q hq p hp c hc h4).symm
  · intro h
    simp only [inGm, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
      decide_eq_true_eq] at h
    intro x hx
    obtain ⟨p, hp, c, hc, rfl⟩ := hx
    rw [Matrix.mulVec_smul]
    refine smul_mem_oVec hc ?_
    rw [app_ofMat, mem_oVec_iff, encV_decV (hlt p)]
    exact h.1 p hp

theorem cert_gmList_length : gmList.length = 1080 :=
  Certificates.certificate7213.1

theorem cert_gmList_nodup : gmList.Nodup :=
  Certificates.certificate7213.2.1

theorem cert_gmList_mem :
    ∀ A ∈ gmList, A.Valid ∧ inGm A = true ∧ A.pow 60 = Mc.one :=
  Certificates.certificate7213.2.2.1

theorem cert_gmList_complete :
    ∀ c0 ∈ List.range 64, ∀ c1 ∈ List.range 64, ∀ c2 ∈ List.range 64,
      inGm ⟨c0, c1, c2⟩ = true → (⟨c0, c1, c2⟩ : Mc) ∈ gmList :=
  Certificates.certificate7213.2.2.2

theorem mem_gm_iff (g : Matrix.GeneralLinearGroup (Fin 3) F4) :
    g ∈ gm ↔ Mc.ofMat g ∈ gmList := by
  rw [mem_gm_iff_inGm]
  constructor
  · intro h
    obtain ⟨h0, h1, h2⟩ := Mc.ofMat_valid (g : Matrix (Fin 3) (Fin 3) F4)
    exact cert_gmList_complete _ (List.mem_range.2 h0) _ (List.mem_range.2 h1) _
      (List.mem_range.2 h2) h
  · intro h
    exact (cert_gmList_mem _ h).2.1

@[expose] noncomputable def glOf (A : Mc) (h : A ∈ gmList) :
    Matrix.GeneralLinearGroup (Fin 3) F4 :=
  ⟨A.toMat, A.toMat ^ 59, by
    obtain ⟨hv, -, hp⟩ := cert_gmList_mem A h
    rw [← pow_succ', ← Mc.toMat_pow hv, hp, Mc.toMat_one], by
    obtain ⟨hv, -, hp⟩ := cert_gmList_mem A h
    rw [← pow_succ, ← Mc.toMat_pow hv, hp, Mc.toMat_one]⟩

theorem coe_glOf (A : Mc) (h : A ∈ gmList) :
    ((glOf A h : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = A.toMat :=
  rfl

theorem ofMat_glOf (A : Mc) (h : A ∈ gmList) :
    Mc.ofMat (glOf A h) = A := by
  rw [coe_glOf, Mc.ofMat_toMat (cert_gmList_mem A h).1]

theorem glOf_mem (A : Mc) (h : A ∈ gmList) : glOf A h ∈ gm := by
  rw [mem_gm_iff, ofMat_glOf]
  exact h

theorem card_gm : Nat.card gm = 1080 := by
  classical
  have e : gm ≃ {A : Mc // A ∈ gmList} :=
    { toFun := fun g => ⟨Mc.ofMat ((g : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4), (mem_gm_iff g).1 g.2⟩
      invFun := fun A => ⟨glOf A.1 A.2, glOf_mem A.1 A.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Units.ext
        rw [coe_glOf, Mc.toMat_ofMat]
      right_inv := fun A => Subtype.ext (ofMat_glOf A.1 A.2) }
  have e2 : {A : Mc // A ∈ gmList} ≃ ↥gmList.toFinset :=
    Equiv.subtypeEquivRight fun A => by simp
  rw [Nat.card_congr (e.trans e2), Nat.card_eq_finsetCard,
    List.toFinset_card_of_nodup cert_gmList_nodup, cert_gmList_length]

end CFSG.Quasithin.H13.S127.Mod

end
