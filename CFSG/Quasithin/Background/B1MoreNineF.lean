module

public import CFSG.Quasithin.Background.B1MoreNineE

public section

namespace CFSG.Quasithin

open CFSG.Open B19Aux

variable {V : Type*} [CommGroup V]

namespace B19Loc

variable {G A : Subgroup (MulAut V)}

theorem FA_mem_Xk [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    FAsub G A ∈ Xk G 1 := by
  obtain ⟨-, hFA3, hW4, -⟩ := P.local_structure hV
  refine ⟨P.FA_le, by simpa using hFA3, ?_⟩
  show rk ↥(commV (FAsub G A)) = 2 * 1
  unfold rk
  rw [hW4]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, padicValNat.prime_pow]

theorem commV_FA_sup_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    commV (FAsub G A) ⊔ fixV (FAsub G A) = ⊤ :=
  (Xk_decomp hV (P.FA_mem_Xk hV)).1

theorem commV_FA_inf_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    commV (FAsub G A) ⊓ fixV (FAsub G A) = ⊥ :=
  (Xk_decomp hV (P.FA_mem_Xk hV)).2

theorem trivial_of_trivial_W_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A)
    {g : MulAut V} (hW : ∀ w ∈ commV (FAsub G A), g w = w) (hF : ∀ z ∈ fixV (FAsub G A), g z = z) :
    g = 1 := by
  ext v
  have hv : v ∈ commV (FAsub G A) ⊔ fixV (FAsub G A) := by
    rw [P.commV_FA_sup_fixV hV]; trivial
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, hW w hw, hF z hz]
  simp

theorem A_trivial_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    ∀ x ∈ fixV (FAsub G A), ∀ a ∈ A, a x = x := by
  obtain ⟨-, -, -, hWcomm, -, hsup, -⟩ := P.local_structure hV
  intro x hx a ha
  have hWinv : ∀ w ∈ commV (FAsub G A), a w ∈ commV (FAsub G A) := by
    intro w hw
    rw [← hWcomm] at hw ⊢
    exact P.W_inv_A ha w hw
  have hxsup : x ∈ commV (FAsub G A) ⊔ fixV A := by rw [hsup]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hxsup
  have h1 : a (w * c) * (w * c)⁻¹ ∈ commV (FAsub G A) := by
    rw [map_mul, hc a ha]
    have e : a w * c * (w * c)⁻¹ = a w * w⁻¹ := by cgroup
    rw [e]
    exact (commV (FAsub G A)).mul_mem (hWinv w hw) ((commV (FAsub G A)).inv_mem hw)
  have h2 : a (w * c) ∈ fixV (FAsub G A) := by
    intro f hf
    have h3 : a⁻¹ * f * a ∈ FAsub G A := by
      have := conj_FA (A.inv_mem ha) hf
      simpa using this
    have h4 := hx _ h3
    simp only [MulAut.mul_apply] at h4
    have h5 : a (a⁻¹ (f (a (w * c)))) = a (w * c) := by rw [h4]
    simpa using h5
  have h4 : a (w * c) * (w * c)⁻¹ ∈ fixV (FAsub G A) :=
    (fixV (FAsub G A)).mul_mem h2 ((fixV (FAsub G A)).inv_mem hx)
  have h5 : a (w * c) * (w * c)⁻¹ ∈ commV (FAsub G A) ⊓ fixV (FAsub G A) := ⟨h1, h4⟩
  rw [P.commV_FA_inf_fixV hV, Subgroup.mem_bot, mul_inv_eq_one] at h5
  exact h5

theorem eq_one_of_trivial_on_W [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A)
    {x : MulAut V} (hx : x ∈ FAsub G A ⊔ A) (hW : ∀ w ∈ commV (FAsub G A), x w = w) : x = 1 := by
  obtain ⟨f, hf, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer (A_normalizes_FA G A)).1 hx
  refine P.trivial_of_trivial_W_fixV hV hW fun z hz => ?_
  rw [MulAut.mul_apply, P.A_trivial_fixV hV z hz a ha]
  exact hz f hf

theorem A'_le_FA_sup_A [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A' : Subgroup (MulAut V)}
    (P : B19Loc G A) (P' : B19Loc G A') (hY : FAsub G A' = FAsub G A) : A' ≤ FAsub G A ⊔ A := by
  intro a' ha'
  obtain ⟨-, -, -, hWcomm, -, -, hHtop, -⟩ := P.local_structure hV
  obtain ⟨-, -, -, hWcomm', -, -, -, -⟩ := P'.local_structure hV
  have hWW : Wsub G A' = Wsub G A := by rw [hWcomm', hWcomm, hY]
  have hinv : ∀ b ∈ A', ∀ w ∈ Wsub G A, b w ∈ Wsub G A := by
    intro b hb w hw
    rw [← hWW] at hw ⊢
    exact P'.W_inv_A hb w hw
  have hstab : a' ∈ stabSub (Wsub G A) :=
    mem_stabSub_of_invariant (hinv a' ha') (hinv a'⁻¹ (A'.inv_mem ha'))
  have hψ : resHom (Wsub G A) ⟨a', hstab⟩ ∈ Fbar G A ⊔ Abar G A := hHtop _
  obtain ⟨φf, hφf, φa, hφa, hψeq⟩ :=
    (mem_sup_iff_of_le_normalizer (Abar_normalizes_Fbar G A)).1 hψ
  obtain ⟨gf, hgf, rfl⟩ := mem_autSub.1 hφf
  obtain ⟨ga, hga, rfl⟩ := mem_autSub.1 hφa
  have hact : ∀ w ∈ Wsub G A, a' w = (gf : MulAut V) ((ga : MulAut V) w) := by
    intro w hw
    have := congrArg (fun φ : MulAut ↥(Wsub G A) => ((φ ⟨w, hw⟩ : ↥(Wsub G A)) : V)) hψeq
    simpa [resHom_apply, MulAut.mul_apply] using this
  have hxmem : (gf : MulAut V) * (ga : MulAut V) ∈ FAsub G A ⊔ A :=
    (FAsub G A ⊔ A).mul_mem (Subgroup.mem_sup_left hgf) (Subgroup.mem_sup_right hga)
  have hxfix : ∀ z ∈ fixV (FAsub G A), ((gf : MulAut V) * (ga : MulAut V)) z = z := by
    intro z hz
    rw [MulAut.mul_apply, P.A_trivial_fixV hV z hz _ hga]
    exact hz _ hgf
  have hg : ((gf : MulAut V) * (ga : MulAut V))⁻¹ * a' = 1 := by
    refine P.trivial_of_trivial_W_fixV hV ?_ ?_
    · intro w hw
      have hw' : w ∈ Wsub G A := by rw [hWcomm]; exact hw
      rw [MulAut.mul_apply, hact w hw']
      simp
    · intro z hz
      have hz' : z ∈ fixV (FAsub G A') := by rw [hY]; exact hz
      rw [MulAut.mul_apply, P'.A_trivial_fixV hV z hz' a' ha']
      calc ((gf : MulAut V) * (ga : MulAut V))⁻¹ z =
            ((gf : MulAut V) * (ga : MulAut V))⁻¹ (((gf : MulAut V) * (ga : MulAut V)) z) := by
              rw [hxfix z hz]
        _ = z := by simp
  have : a' = (gf : MulAut V) * (ga : MulAut V) := (inv_mul_eq_one.1 hg).symm
  rw [this]
  exact hxmem

theorem GY_equiv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    Nonempty (↥(FAsub G A ⊔ A) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨-, -, -, hWcomm, -, -, -, ⟨e⟩⟩ := P.local_structure hV
  have hle : FAsub G A ⊔ A ≤ stabSub (Wsub G A) := sup_le (FA_le_stab G A) P.A_le_stab
  let ρ : ↥(FAsub G A ⊔ A) →* MulAut ↥(Wsub G A) :=
    (resHom (Wsub G A)).comp (Subgroup.inclusion hle)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hW : ∀ w ∈ commV (FAsub G A), (x : MulAut V) w = w := by
      intro w hw
      have hw' : w ∈ Wsub G A := by rw [hWcomm]; exact hw
      have := congrArg (fun φ : MulAut ↥(Wsub G A) => ((φ ⟨w, hw'⟩ : ↥(Wsub G A)) : V)) hx
      simpa [ρ, resHom_apply] using this
    exact Subtype.ext (P.eq_one_of_trivial_on_W hV x.2 hW)
  have hrange : ρ.range = Hbar G A := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨f, hf, a, ha, hxeq⟩ := (mem_sup_iff_of_le_normalizer (A_normalizes_FA G A)).1 x.2
      have hfs : f ∈ stabSub (Wsub G A) := FA_le_stab G A hf
      have has : a ∈ stabSub (Wsub G A) := P.A_le_stab ha
      have h1 : (⟨(x : MulAut V), hle x.2⟩ : ↥(stabSub (Wsub G A))) = ⟨f, hfs⟩ * ⟨a, has⟩ :=
        Subtype.ext hxeq
      have h2 : ρ x = resHom (Wsub G A) ⟨f, hfs⟩ * resHom (Wsub G A) ⟨a, has⟩ := by
        show resHom (Wsub G A) ⟨(x : MulAut V), hle x.2⟩ = _
        rw [h1, map_mul]
      rw [h2]
      exact Subgroup.mul_mem_sup (mem_autSub.2 ⟨⟨f, hfs⟩, hf, rfl⟩) (mem_autSub.2 ⟨⟨a, has⟩, ha, rfl⟩)
    · refine sup_le ?_ ?_
      · intro φ hφ
        obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
        exact ⟨⟨(g : MulAut V), Subgroup.mem_sup_left hg⟩, rfl⟩
      · intro φ hφ
        obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
        exact ⟨⟨(g : MulAut V), Subgroup.mem_sup_right hg⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans ((MulEquiv.subgroupCongr hrange).trans e)⟩

end B19Loc

end CFSG.Quasithin
