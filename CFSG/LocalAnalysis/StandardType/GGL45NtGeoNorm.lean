module

public import CFSG.LocalAnalysis.StandardType.GGL45NtCoreGeo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45NtGeoNormRaw (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ (Ebar : Subgroup (MulAut R)) (f : MulAut R), f ∈ F → orderOf f = p →
      IsElemAbelian p Ebar → p ^ 2 ≤ Nat.card Ebar → (∀ e ∈ Ebar, e ∈ I) →
      (∀ e ∈ Ebar, e * f = f * e) →
      (∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) →
      GGL45NtGeo p I Ebar f

@[expose] def GGL45NtGeoNormOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun p _ => GGL45NtGeoNormRaw p

private lemma ggL45NtGeoNorm_isElemAbelian_map {p : ℕ} {R : Type} [Group R]
    {E : Subgroup (MulAut R)} (hE : IsElemAbelian p E) (g : MulAut R) :
    IsElemAbelian p (E.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hbeq⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hcomm' : a' * b' = b' * a' := by
      have h := hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      simpa using congrArg Subtype.val h
    rw [← haeq, ← hbeq, ← map_mul, ← map_mul, hcomm']
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 x' hx', map_one]

private lemma ggL45NtGeoNorm_CIp_map {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {Ebar E' : Subgroup (MulAut R)} {u : MulAut R}
    (hφI : ∀ {x : MulAut R}, x ∈ I → MulAut.conj u⁻¹ x ∈ I)
    (hE' : E' = Ebar.map (MulAut.conj u⁻¹).toMonoidHom)
    {x : MulAut R} (hx : GGL45NtCIp p I Ebar x) :
    GGL45NtCIp p I E' (MulAut.conj u⁻¹ x) := by
  obtain ⟨hxI, hxcomm, hxP⟩ := hx
  refine ⟨hφI hxI, ?_, ?_⟩
  · intro e' he'
    rw [hE'] at he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    show MulAut.conj u⁻¹ x * MulAut.conj u⁻¹ e = MulAut.conj u⁻¹ e * MulAut.conj u⁻¹ x
    rw [← map_mul, ← map_mul, hxcomm e he]
  · obtain ⟨k, hk⟩ := hxP
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩

private lemma ggL45NtGeoNorm_conj {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {Ebar E' : Subgroup (MulAut R)} {f u : MulAut R}
    (hφI : ∀ {x : MulAut R}, x ∈ I → MulAut.conj u⁻¹ x ∈ I)
    (hψI : ∀ {x : MulAut R}, x ∈ I → MulAut.conj u x ∈ I)
    (hE' : E' = Ebar.map (MulAut.conj u⁻¹).toMonoidHom)
    (hgeo : GGL45NtGeo p I E' f) :
    GGL45NtGeo p I Ebar (u * f * u⁻¹) := by
  obtain ⟨g1, g2c, N, hN2, gN, g3⟩ := hgeo
  have hψφ : ∀ x : MulAut R, MulAut.conj u ((MulAut.conj u)⁻¹ x) = x := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_inv_apply]
    group
  have hφψ : ∀ x : MulAut R, (MulAut.conj u)⁻¹ (MulAut.conj u x) = x := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_inv_apply]
    group
  have hψφ' : ∀ x : MulAut R, MulAut.conj u (MulAut.conj u⁻¹ x) = x := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  refine ⟨?_, ?_, N, hN2, ?_, ?_⟩
  · intro x y hx hy
    have hx' := ggL45NtGeoNorm_CIp_map hφI hE' hx
    have hy' := ggL45NtGeoNorm_CIp_map hφI hE' hy
    have h := congrArg (MulAut.conj u) (g1 _ _ hx' hy')
    simpa only [map_mul, map_inv, hψφ] using h
  · intro x hx w hwI hwcomm
    have hx' := ggL45NtGeoNorm_CIp_map hφI hE' hx
    have hwcomm' : ∀ e' ∈ E', MulAut.conj u⁻¹ w * e' = e' * MulAut.conj u⁻¹ w := by
      intro e' he'
      rw [hE'] at he'
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
      show MulAut.conj u⁻¹ w * MulAut.conj u⁻¹ e = MulAut.conj u⁻¹ e * MulAut.conj u⁻¹ w
      rw [← map_mul, ← map_mul, hwcomm e he]
    have h := g2c (MulAut.conj u⁻¹ x) hx' (MulAut.conj u⁻¹ w) (hφI hwI) hwcomm'
    have h' := congrArg (MulAut.conj u) h
    simpa only [map_mul, map_inv, hψφ] using h'
  · intro a ha
    have ha' := ggL45NtGeoNorm_CIp_map hφI hE' ha
    have h := gN (MulAut.conj u⁻¹ a) ha'
    have key : (u * f * u⁻¹) * a * (u * f * u⁻¹)⁻¹
        = u * (f * MulAut.conj u⁻¹ a * f⁻¹) * u⁻¹ := by
      rw [MulAut.conj_apply]
      group
    have hconja : u * MulAut.conj u⁻¹ a * u⁻¹ = a := by
      rw [MulAut.conj_apply]
      group
    rw [key, h, ← conj_pow (a := u) (b := MulAut.conj u⁻¹ a) (i := N), hconja]
  · intro a ha hfix
    have ha' := ggL45NtGeoNorm_CIp_map hφI hE' ha
    have hfix' : f * MulAut.conj u⁻¹ a * f⁻¹ = MulAut.conj u⁻¹ a := by
      have hfix0 : MulAut.conj u f * a * (MulAut.conj u f)⁻¹ = a := by
        rw [MulAut.conj_apply u f]
        exact hfix
      have h := congrArg (MulAut.conj u⁻¹) hfix0
      simpa only [map_mul, map_inv, hφψ] using h
    obtain ⟨b', hb', hb'eq⟩ := g3 (MulAut.conj u⁻¹ a) ha' hfix'
    refine ⟨MulAut.conj u b', ?_, ?_⟩
    · refine ⟨hψI hb'.1, ?_, ?_⟩
      · intro e he
        have hmem : MulAut.conj u⁻¹ e ∈ E' := by
          rw [hE']
          exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩
        have hcomm' := hb'.2.1 (MulAut.conj u⁻¹ e) hmem
        show MulAut.conj u b' * e = e * MulAut.conj u b'
        calc MulAut.conj u b' * e
            = MulAut.conj u b' * MulAut.conj u (MulAut.conj u⁻¹ e) := by rw [hψφ' e]
          _ = MulAut.conj u (b' * MulAut.conj u⁻¹ e) := by rw [← map_mul]
          _ = MulAut.conj u (MulAut.conj u⁻¹ e * b') := by rw [hcomm']
          _ = MulAut.conj u (MulAut.conj u⁻¹ e) * MulAut.conj u b' := by rw [map_mul]
          _ = e * MulAut.conj u b' := by rw [hψφ' e]
      · obtain ⟨k, hk⟩ := hb'.2.2
        exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · have h := congrArg (MulAut.conj u) hb'eq
      simpa only [map_pow, hψφ'] using h

theorem ggL45NtGeo_of_normalized {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I)
    (h : ∀ (Ebar : Subgroup (MulAut R)) (f : MulAut R), f ∈ F → orderOf f = p →
      IsElemAbelian p Ebar → p ^ 2 ≤ Nat.card Ebar → (∀ e ∈ Ebar, e ∈ I) →
      (∀ e ∈ Ebar, e * f = f * e) →
      (∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) →
      GGL45NtGeo p I Ebar f) :
    ∀ (Ebar : Subgroup (MulAut R)) (f' : MulAut R), GGL45NtCoreHyp p I F Ebar f' →
      GGL45NtGeo p I Ebar f' := by
  intro Ebar f' hcore
  obtain ⟨hEab, hEcard, hEsub, _hf'p, ⟨f, hfF, u, huI, hforder, hf'eq⟩, hcomm, hsat⟩ := hcore
  obtain ⟨J, hJ⟩ := hI
  have hmem : ∀ x : MulAut R, x ∈ J ↔ x ∈ I := fun x => Set.ext_iff.mp hJ x
  have hconjJ : ∀ (g : MulAut R), g ∈ J → ∀ x ∈ J, g * x * g⁻¹ ∈ J :=
    fun g hg x hx => J.mul_mem (J.mul_mem hg hx) (J.inv_mem hg)
  let E' : Subgroup (MulAut R) := Ebar.map (MulAut.conj u⁻¹).toMonoidHom
  have hE'def : E' = Ebar.map (MulAut.conj u⁻¹).toMonoidHom := rfl
  have hφI : ∀ {x : MulAut R}, x ∈ I → MulAut.conj u⁻¹ x ∈ I := by
    intro x hx
    rw [MulAut.conj_apply]
    exact (hmem _).mp (hconjJ u⁻¹ (J.inv_mem ((hmem u).mpr huI)) x ((hmem x).mpr hx))
  have hψI : ∀ {x : MulAut R}, x ∈ I → MulAut.conj u x ∈ I := by
    intro x hx
    rw [MulAut.conj_apply]
    exact (hmem _).mp (hconjJ u ((hmem u).mpr huI) x ((hmem x).mpr hx))
  have hψφ : ∀ x : MulAut R, MulAut.conj u (MulAut.conj u⁻¹ x) = x := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hφψ : ∀ x : MulAut R, MulAut.conj u⁻¹ (MulAut.conj u x) = x := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hE'ab : IsElemAbelian p E' := by
    rw [hE'def]
    exact ggL45NtGeoNorm_isElemAbelian_map hEab u⁻¹
  have hE'card : p ^ 2 ≤ Nat.card E' := by
    rw [hE'def]
    rw [Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective]
    exact hEcard
  have hE'sub : ∀ e' ∈ E', e' ∈ I := by
    intro e' he'
    rw [hE'def] at he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    exact hφI (hEsub e he)
  have hE'f : ∀ e' ∈ E', e' * f = f * e' := by
    intro e' he'
    rw [hE'def] at he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    show MulAut.conj u⁻¹ e * f = f * MulAut.conj u⁻¹ e
    have hf'conj : f' = MulAut.conj u f := hf'eq
    have heq : e * MulAut.conj u f = MulAut.conj u f * e := by
      have h := hcomm e he
      rwa [hf'conj] at h
    have h' := congrArg (MulAut.conj u⁻¹) heq
    simpa only [map_mul, hφψ] using h'
  have hE'sat : ∀ r : R, r ^ p = 1 → (∀ e' ∈ E', e' r = r) → f r = r → MulAut.conj r ∈ E' := by
    intro r hr hrE' hfr
    let r' : R := u r
    have hr'p : r' ^ p = 1 := by
      show (u r) ^ p = 1
      rw [← map_pow, hr, map_one]
    have hEr' : ∀ e ∈ Ebar, e r' = r' := by
      intro e he
      have hmem' : MulAut.conj u⁻¹ e ∈ E' := by
        rw [hE'def]
        exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩
      have h := hrE' (MulAut.conj u⁻¹ e) hmem'
      have heu : e * u = u * MulAut.conj u⁻¹ e := by
        rw [MulAut.conj_apply]
        group
      show e (u r) = u r
      calc e (u r) = (e * u) r := rfl
        _ = (u * MulAut.conj u⁻¹ e) r := by rw [heu]
        _ = u ((MulAut.conj u⁻¹ e) r) := rfl
        _ = u r := by rw [h]
    have hfr' : (u * f * u⁻¹) r' = r' := by
      show (u * f * u⁻¹) (u r) = u r
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfr]
    have hfr'' : f' r' = r' := by
      rw [hf'eq]
      exact hfr'
    have hsat' : MulAut.conj r' ∈ Ebar := hsat r' hr'p hEr' hfr''
    rw [hE'def]
    refine Subgroup.mem_map.mpr ⟨MulAut.conj r', hsat', ?_⟩
    show MulAut.conj u⁻¹ (MulAut.conj r') = MulAut.conj r
    have hr'conj : MulAut.conj r' = u * MulAut.conj r * u⁻¹ := by
      rw [show r' = u r from rfl]
      ext x
      simp only [MulAut.conj_apply, MulAut.mul_apply]
      rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
    rw [hr'conj, MulAut.conj_apply]
    group
  have hgeo' : GGL45NtGeo p I E' f := h E' f hfF hforder hE'ab hE'card hE'sub hE'f hE'sat
  have hgeo'' : GGL45NtGeo p I Ebar (u * f * u⁻¹) :=
    ggL45NtGeoNorm_conj hφI hψI hE'def hgeo'
  rw [hf'eq]
  exact hgeo''

end CFSG.StandardType
