module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClGlobal

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem mem_of_orth_pointRad (hnd : F.Nondegenerate) (halt : F.IsAlt) {H : Subgroup (V ≃ₗ[K] V)}
    {e f : V} (hef : F e f = 1) {Q : QuadraticForm K V} (hQ : Q.polarBilin = F) (he : Q e = 0)
    (hfull : ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hHQ : H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ orthSubgroup Q ⊓ pointRadSubgroup F e) : g ∈ H := by
  obtain ⟨hgO, hgP⟩ := hg
  have hfe : F f e = 1 := by
    rw [form_comm halt]
    exact hef
  have hωe : F (g f - f) e = 0 := pointRad_om_perp hgP
  obtain ⟨d, ⟨hdH, hdP⟩, c, hdc⟩ := hfull.om hnd halt hef (fun x hx => hx.2) hωe
  have hdP' : d ∈ pointRadSubgroup F e := hdP
  have hdO : d ∈ orthSubgroup Q := hHQ ⟨hdH, hdP'⟩
  have h1 := (pointRad_mem_orth_iff halt hef hQ he hgP).mp hgO
  have h2 := (pointRad_mem_orth_iff halt hef hQ he hdP').mp hdO
  rw [hdc, qf_add hQ, qf_smul, he] at h2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hωe,
    hfe] at h2
  have hc0 : c = 0 := by
    linear_combination h1 - h2
  have hdf : d f = g f := by
    rw [hc0, zero_smul, add_zero] at hdc
    have : d f - f = g f - f := hdc
    exact sub_left_injective this
  have : d = g := pointRad_ext halt hef hdP' hgP hdf
  rw [← this]
  exact hdH

theorem exists_pointRad_of_singular (hnd : F.Nondegenerate) (halt : F.IsAlt)
    {H : Subgroup (V ≃ₗ[K] V)} {e f : V} (hef : F e f = 1) {Q : QuadraticForm K V}
    (hQ : Q.polarBilin = F) (he : Q e = 0) (hf : Q f = 0)
    (hfull : ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hHQ : H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q) {s : V} (hes : F e s = 1) (hs : Q s = 0) :
    ∃ g ∈ H ⊓ pointRadSubgroup F e, g f = s := by
  have hfe : F f e = 1 := by
    rw [form_comm halt]
    exact hef
  have hse : F s e = 1 := by
    rw [form_comm halt]
    exact hes
  have hωe : F (s - f) e = 0 := by
    rw [map_sub, LinearMap.sub_apply, hse, hfe, sub_self]
  obtain ⟨d, ⟨hdH, hdP⟩, c, hdc⟩ := hfull.om hnd halt hef (fun x hx => hx.2) hωe
  have hdP' : d ∈ pointRadSubgroup F e := hdP
  have hdO : d ∈ orthSubgroup Q := hHQ ⟨hdH, hdP'⟩
  have h2 := (pointRad_mem_orth_iff halt hef hQ he hdP').mp hdO
  rw [hdc, qf_add hQ, qf_smul, he] at h2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hωe,
    hfe] at h2
  have hsf : s = f + (s - f) := by abel
  have h3 : Q s = Q f + Q (s - f) + F f (s - f) := by
    conv_lhs => rw [hsf]
    exact qf_add hQ f (s - f)
  rw [hs, hf] at h3
  have hc0 : c = 0 := by
    linear_combination (-1 : K) * h2 + (-1 : K) * h3 -
      (F f (s - f)) * (two_eq_zero_K (K := K))
  refine ⟨d, ⟨hdH, hdP'⟩, ?_⟩
  rw [hc0, zero_smul, add_zero] at hdc
  have : d f = f + (s - f) := by
    rw [← hdc]
    abel
  rw [this]
  abel

theorem eq_commutator_of_global_form (hSiegel : SiegelGenStatement) (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (hq : 4 ≤ Nat.card K) (hdim : 4 ≤ Module.finrank K V)
    {H : Subgroup (V ≃ₗ[K] V)} (hne : (ElPts F H).Nonempty)
    (hspan : Submodule.span K (ElPts F H) = ⊤)
    (hgen : H = Subgroup.closure (⋃ e ∈ ElPts F H, (H : Set _) ∩ pointRad F e))
    (hH : H ≤ sympSubgroup F) {Q : QuadraticForm K V} (hQ : Q.polarBilin = F)
    (hQ0 : ∀ e ∈ ElPts F H, Q e = 0 ∧ H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q) :
    H = ⁅orthSubgroup Q, orthSubgroup Q⁆ := by
  obtain ⟨e₀, he₀⟩ := hne
  have hSing : {e : V | e ≠ 0 ∧ Q e = 0} = ElPts F H := by
    ext s
    constructor
    · rintro ⟨hs0, hsQ⟩
      have hex : ∃ e ∈ ElPts F H, F e s ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hs0 (eq_zero_of_perp_span hnd hspan fun e he => by
          rw [form_comm halt]
          exact hcon e he)
      obtain ⟨e, he, hes⟩ := hex
      obtain ⟨r, hr, her⟩ := exists_partner_ElPts hnd hspan he
      have hf : (F e r)⁻¹ • r ∈ ElPts F H := ElPts_smul (inv_ne_zero her) hr
      have hef : F e ((F e r)⁻¹ • r) = 1 := pairing_normalize her
      have hfQ := (hQ0 _ hf).1
      have hs' : F e ((F e s)⁻¹ • s) = 1 := pairing_normalize hes
      have hs'Q : Q ((F e s)⁻¹ • s) = 0 := quadForm_smul_zero Q hsQ
      obtain ⟨g, hg, hgf⟩ := exists_pointRad_of_singular hnd halt hef hQ (hQ0 e he).1 hfQ
        ((mem_ElPts_iff e).mp he).2 (hQ0 e he).2 hs' hs'Q
      have h1 : (F e s)⁻¹ • s ∈ ElPts F H := by
        rw [← hgf]
        exact ElPts_invariant hH hg.1 hf
      have h2 := ElPts_smul hes h1
      rwa [smul_smul, mul_inv_cancel₀ hes, one_smul] at h2
    · intro he
      exact ⟨((mem_ElPts_iff s).mp he).1, (hQ0 s he).1⟩
  have hcong : ∀ e ∈ ElPts F H, (orthSubgroup Q : Set _) ∩ pointRad F e =
      (H : Set _) ∩ pointRad F e := by
    intro e he
    ext g
    constructor
    · rintro ⟨hgO, hgP⟩
      obtain ⟨r, hr, her⟩ := exists_partner_ElPts hnd hspan he
      have hef : F e ((F e r)⁻¹ • r) = 1 := pairing_normalize her
      exact ⟨mem_of_orth_pointRad hnd halt hef hQ (hQ0 e he).1 ((mem_ElPts_iff e).mp he).2
        (hQ0 e he).2 ⟨hgO, hgP⟩, hgP⟩
    · rintro ⟨hgH, hgP⟩
      exact ⟨(hQ0 e he).2 ⟨hgH, hgP⟩, hgP⟩
  have hS := hSiegel K V Q hq (by rw [hQ]; exact hnd) hdim ⟨e₀, ((mem_ElPts_iff e₀).mp he₀).1,
    (hQ0 e₀ he₀).1⟩
  rw [hSing, hQ] at hS
  have hU : (⋃ e ∈ ElPts F H, (H : Set _) ∩ pointRad F e) =
      ⋃ e ∈ ElPts F H, (orthSubgroup Q : Set _) ∩ pointRad F e :=
    Set.iUnion₂_congr fun e he => (hcong e he).symm
  rw [hS, ← hU]
  exact hgen

end CFSG.RankThree.GF2n.Stroth80.Classify
