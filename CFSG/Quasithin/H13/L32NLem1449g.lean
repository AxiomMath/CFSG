module

public import CFSG.Quasithin.H13.L32NLem1449f
public import CFSG.Quasithin.H13.L32NLem1449c

public section

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert Q1449Cert L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

@[expose] noncomputable def preH (D : HatModelU (fsuU T V))
    (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (A : Subgroup (GL (Fin 8) (ZMod 2))) : Subgroup G :=
  (A.comap (hom8 D e (HN (T := T) (V := V)))).map (l32nH T V).subtype

omit [Finite G] in
theorem mem_preH {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {A : Subgroup (GL (Fin 8) (ZMod 2))}
    {n : G} : n ∈ preH D e A ↔ ∃ hn : n ∈ l32nH T V, matOf e (D.ρ ⟨n, HN hn⟩) ∈ A := by
  constructor
  · rintro ⟨⟨n, hn⟩, hA, rfl⟩
    exact ⟨hn, hA⟩
  · rintro ⟨hn, hA⟩
    exact ⟨⟨n, hn⟩, hA, rfl⟩

theorem zmod2_eq_zero_or_one : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem sylow_of_normalizer_le {M X S : Subgroup G} (hS : IsSylowTwoOf S (M ⊓ X))
    (hN : X ⊓ Subgroup.normalizer (S : Set G) ≤ M) : IsSylowTwoOf S X := by
  have hSX : S ≤ X := hS.1.trans inf_le_right
  obtain ⟨R, hR, hSR⟩ := A4.exists_isSylowTwoOf_ge hSX hS.2.1
  rcases eq_or_lt_of_le hSR with h | h
  · rw [h]
    exact hR
  · exfalso
    obtain ⟨s, hsR, hsN, hsS⟩ := A4.exists_mem_normalizer_not_mem hR.2.1 h
    have hsM : s ∈ M := hN ⟨hR.1 hsR, hsN⟩
    have hmax := (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 (R ⊓ M)
      (fun x hx => ⟨hx.2, hR.1 hx.1⟩) (hR.2.1.to_inf_left) (le_inf hSR (hS.1.trans inf_le_left))
    exact hsS (hmax ⟨hsR, hsM⟩)

omit [Finite G] in
theorem preH_le_H {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {A : Subgroup (GL (Fin 8) (ZMod 2))} :
    preH D e A ≤ l32nH T V := fun _ hn => (mem_preH.mp hn).1

omit [Finite G] in
theorem le_normalizer_R (X : Subgroup G) :
    X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

namespace Good

section Basic

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem cent_U {w : G} (hw : ∀ u ∈ fsuU T V, w * u = u * w) : w ∈ fsuV1 T V := by
  obtain ⟨_, S⟩ := C.base.set14
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  have hzU : z ∈ fsuU T V := V_le_U (C.base.plane.1.1 (C.base.plane.2 hz))
  have hwH : w ∈ l32nH T V := S.mem_g1 hz hz1 (by rw [hw z hzU]; group)
  have hwU : w ∈ fsuU T V := by
    refine C.mem_U_of_star hwH ?_
    rw [(L128A.HatU.rho_eq_one_iff D ⟨w, HN hwH⟩).mpr fun u hu => ?_, map_one]
    rw [show w * u * w⁻¹ * u⁻¹ = 1 by rw [hw u hu]; group]
    exact one_mem _
  rw [← C.base.zU]
  exact ⟨hwU, Subgroup.mem_centralizer_iff.mpr fun u hu => (hw u hu).symm⟩

theorem U_le_preH : fsuU T V ≤ preH D e (cenA c x₀) := fun u hu =>
  mem_preH.mpr ⟨C.UH hu, by rw [C.star_U hu]; exact one_mem _⟩

theorem dI_two : IsPGroup 2 ↥(dI T V i) := fun d => ⟨1, Subtype.ext (by
  rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]
  exact C.dI_sq d.2)⟩

theorem dI_le_R : dI T V i ≤ pCoreOf 2 (Subgroup.normalizer (dI T V i : Set G)) :=
  CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ C.dI_two

end Basic

section Cert

variable
  {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem preH_le_normalizer : preH D e (cenA c x₀) ≤ Subgroup.normalizer (dI T V i : Set G) := by
  intro n hn
  obtain ⟨hnH, hnA⟩ := mem_preH.mp hn
  exact Subgroup.mem_normalizer_fintype fun d hd =>
    C.conj_mem_dI hnH (comm_of_mem_cenA C.hc hnA) hd

theorem U_inf_R (hout : ∃ w ∈ Subgroup.normalizer (dI T V i : Set G), w ∉ l32nH T V) :
    fsuU T V ⊓ pCoreOf 2 (Subgroup.normalizer (dI T V i : Set G)) = rI T V i := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S⟩ := C.base.set14
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  set X := Subgroup.normalizer (dI T V i : Set G) with hX
  set R := pCoreOf 2 X with hR
  have hdR : dI T V i ≤ R := C.dI_le_R
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := le_normalizer_R _
  have hrM : rI T V i ≤ fsuU T V ⊓ R := le_inf rI_le_U (rI_le_dI.trans hdR)
  refine le_antisymm ?_ hrM
  by_contra hne
  rw [IsConcreteLE.not_le_iff_exists] at hne
  obtain ⟨m, hm, hmr⟩ := hne
  set M := fsuU T V ⊓ R with hM
  let W : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
    { carrier := {w | ∃ m ∈ M, e (D.π m) = w}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, M.mul_mem ha hb, by rw [D.π_mul _ ha.1 _ hb.1, map_add]⟩
      zero_mem' := ⟨1, M.one_mem, by rw [L128A.HatU.π_one, map_zero]⟩
      smul_mem' := by
        rintro t _ ⟨a, ha, rfl⟩
        rcases zmod2_eq_zero_or_one t with rfl | rfl
        · exact ⟨1, M.one_mem, by rw [L128A.HatU.π_one, map_zero, zero_smul]⟩
        · exact ⟨a, ha, by rw [one_smul]⟩ }
  have hall : ∀ w, w ∈ W := by
    refine eq_top_of_irr C.hc C.hx₀ W (fun v hv => ?_) (fun a ha v hv => ?_)
      (show e (D.π m) ∈ W from ⟨m, hm, rfl⟩) (fun h => hmr ((C.mem_rI_iff hm.1).mpr h))
    · obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm v)
      have hur : u ∈ rI T V i :=
        (C.mem_rI_iff hu).mpr (by rw [hue, LinearEquiv.apply_symm_apply]; exact hv)
      exact ⟨u, hrM hur, by rw [hue, LinearEquiv.apply_symm_apply]⟩
    · obtain ⟨m', hm', rfl⟩ := hv
      have haΓ : a ∈ img8 D e (l32nH T V) := by rw [C.imgH]; exact (cenA_le C.hc x₀ ha).1
      obtain ⟨h, hh, hhN, rfl⟩ := (mem_img8 D e).mp haΓ
      have hhX : h ∈ X := C.preH_le_normalizer (mem_preH.mpr ⟨hh, ha⟩)
      refine ⟨h * m' * h⁻¹, ⟨L128A.HatU.conj_mem (HN hh) hm'.1,
        (Subgroup.mem_normalizer_iff.mp (hXR hhX) m').mp hm'.2⟩, ?_⟩
      rw [matOf_mulVec, D.ρ_π _ m' hm'.1]
  have hUR : fsuU T V ≤ R := fun u hu => by
    obtain ⟨m', hm', hm'e⟩ := hall (e (D.π u))
    have h1 : D.π m' = D.π u := e.injective hm'e
    have h2 := (D.π_eq_iff _ hm'.1 _ hu).mp h1
    rw [C.base.zU] at h2
    have h3 := M.mul_mem hm' (hrM (C.V1_le_rI h2))
    rw [mul_inv_cancel_left] at h3
    exact h3.2
  obtain ⟨w, hwX, hwH⟩ := hout
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have : Nontrivial ↥R := ⟨⟨⟨i, hdR y_mem_dI⟩, 1, fun h => C.y_not_mem_U (by
    have h' : i = 1 := congrArg Subtype.val h
    rw [h']
    exact one_mem _)⟩⟩
  have := hR2.center_nontrivial
  obtain ⟨c₀, hc₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥R))
  have hcz : ∀ c : G, (∀ r ∈ R, c * r = r * c) → c ≠ 1 → c = z := by
    intro c hcc hc1
    have hcV : c ∈ fsuV1 T V := C.cent_U fun u hu => hcc u (hUR hu)
    rcases S.eq_of_mem_V1 hz hz1 hcV with h | h
    · exact absurd h hc1
    · exact h
  have hc₀c : ∀ r ∈ R, ((c₀ : ↥R) : G) * r = r * (c₀ : ↥R) := fun r hr => by
    have := Subgroup.mem_center_iff.mp c₀.2 ⟨r, hr⟩
    exact (congrArg Subtype.val this).symm
  have hc₀z : ((c₀ : ↥R) : G) = z := hcz _ hc₀c (fun h => hc₀ (Subtype.ext (Subtype.ext h)))
  have hzR : z ∈ R := hc₀z ▸ (c₀ : ↥R).2
  have hzc : ∀ r ∈ R, z * r = r * z := hc₀z ▸ hc₀c
  have hwzc : ∀ r ∈ R, (w * z * w⁻¹) * r = r * (w * z * w⁻¹) := by
    intro r hr
    have hr' : w⁻¹ * r * w ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hXR (X.inv_mem hwX)) r).mp hr
      simpa using this
    have := hzc _ hr'
    calc w * z * w⁻¹ * r = w * (z * (w⁻¹ * r * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * r * w) * z) * w⁻¹ := by rw [this]
      _ = r * (w * z * w⁻¹) := by group
  have hwz1 : w * z * w⁻¹ ≠ 1 := fun h => hz1 (by
    have h' : z = w⁻¹ * (w * z * w⁻¹) * w := by group
    rw [h', h]
    group)
  exact hwH (S.mem_g1 hz hz1 (hcz _ hwzc hwz1))

theorem exists_sylow : ∃ S₀ : Subgroup G,
    IsSylowTwoOf S₀ (Subgroup.normalizer (dI T V i : Set G)) ∧
      S₀ ≤ Subgroup.normalizer (preH D e (cenA c x₀) : Set G) := by
  obtain ⟨_, S⟩ := C.base.set14
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  have hzU : z ∈ fsuU T V := V_le_U (C.base.plane.1.1 (C.base.plane.2 hz))
  set X := Subgroup.normalizer (dI T V i : Set G) with hX
  obtain ⟨S₀, hS₀, hUS⟩ := A4.exists_isSylowTwoOf_ge (le_inf C.UH C.U_le_normalizer_dI) C.U_two
  refine ⟨S₀, sylow_of_normalizer_le hS₀ fun w hw => ?_, fun s hs => ?_⟩
  ·
    have hwN := hw.2
    have hwz : w * z * w⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.mp hwN z).mp (hUS hzU)
    refine S.mem_g1 hz hz1 ?_
    have hcz : w * z * w⁻¹ ∈ fsuV1 T V := C.cent_U fun u hu => by
      have hu' : w⁻¹ * u * w ∈ S₀ := by
        have hwN' := (Subgroup.normalizer (S₀ : Set G)).inv_mem hwN
        have := (Subgroup.mem_normalizer_iff.mp hwN' u).mp (hUS hu)
        simpa using this
      have h1 : (w⁻¹ * u * w) * z = z * (w⁻¹ * u * w) :=
        (C.comm_V1 ((hS₀.1.trans inf_le_left) hu') hz)
      calc w * z * w⁻¹ * u = w * (z * (w⁻¹ * u * w)) * w⁻¹ := by group
        _ = w * ((w⁻¹ * u * w) * z) * w⁻¹ := by rw [h1]
        _ = u * (w * z * w⁻¹) := by group
    rcases S.eq_of_mem_V1 hz hz1 hcz with h | h
    · exfalso
      apply hz1
      have h' : z = w⁻¹ * (w * z * w⁻¹) * w := by group
      rw [h', h]
      group
    · exact h
  ·
    have hsH : s ∈ l32nH T V := (hS₀.1.trans inf_le_left) hs
    have hsX : s ∈ X := (hS₀.1.trans inf_le_right) hs
    have hsi : s * i * s⁻¹ ∈ dI T V i := (Subgroup.mem_normalizer_iff.mp hsX i).mp y_mem_dI
    have hsiU : s * i * s⁻¹ ∉ fsuU T V := fun h => C.y_not_mem_U (by
      have := L128A.HatU.conj_mem (HN ((l32nH T V).inv_mem hsH)) h
      simpa [mul_assoc] using this)
    have hsi' : s * i * s⁻¹ * i ∈ rI T V i := by
      rcases C.mem_dI_iff.mp hsi with h | h
      · exact absurd h.1 hsiU
      · exact h
    have hcomm : matOf e (D.ρ ⟨s, HN hsH⟩) * x₀ = x₀ * matOf e (D.ρ ⟨s, HN hsH⟩) := by
      have h1 := C.star_U hsi'.1
      have hH1 : s * i * s⁻¹ ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).mul_mem hsH C.yH)
        ((l32nH T V).inv_mem hsH)
      have e1 : matOf e (D.ρ ⟨s * i * s⁻¹ * i, HN (C.UH hsi'.1)⟩) =
          matOf e (D.ρ ⟨s, HN hsH⟩) * x₀ * (matOf e (D.ρ ⟨s, HN hsH⟩))⁻¹ * x₀ := by
        rw [star8_mul hH1 C.yH, star8_mul ((l32nH T V).mul_mem hsH C.yH)
          ((l32nH T V).inv_mem hsH), star8_mul hsH C.yH, star8_inv hsH, C.yStar]
      rw [h1] at e1
      have hx0inv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right (x0_sq C.hc C.hx₀)
      calc matOf e (D.ρ ⟨s, HN hsH⟩) * x₀ =
          (matOf e (D.ρ ⟨s, HN hsH⟩) * x₀ * (matOf e (D.ρ ⟨s, HN hsH⟩))⁻¹ * x₀) *
            (x₀⁻¹ * matOf e (D.ρ ⟨s, HN hsH⟩)) := by group
        _ = x₀⁻¹ * matOf e (D.ρ ⟨s, HN hsH⟩) := by rw [← e1, one_mul]
        _ = x₀ * matOf e (D.ρ ⟨s, HN hsH⟩) := by rw [hx0inv]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨hnH, hnA⟩ := mem_preH.mp hn
    have hsn : s * n * s⁻¹ ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem hsH hnH) ((l32nH T V).inv_mem hsH)
    refine mem_preH.mpr ⟨hsn, ?_⟩
    rw [star8_mul ((l32nH T V).mul_mem hsH hnH) ((l32nH T V).inv_mem hsH), star8_mul hsH hnH,
      star8_inv hsH]
    have hsΓ : matOf e (D.ρ ⟨s, HN hsH⟩) ∈ gam c := by
      rw [← C.imgH]
      exact (mem_img8 D e).mpr ⟨s, hsH, HN hsH, rfl⟩
    exact conj_mem_cenA C.hc hsΓ hcomm hnA

end Cert

end Good

end CFSG.Quasithin.H13.L1449
