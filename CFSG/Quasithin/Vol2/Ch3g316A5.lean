module

public import CFSG.Quasithin.Vol2.Ch3n317A5

public section

open Equiv

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.Ch3n317A5
open scoped commutatorElement

section PerComponent

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem a5Gen_fourGroup_le_autI {H T K D : Subgroup G}
    {L : Subgroup (MulAut (IntMod V hV))} (θ : L ≃* Perm (Fin 5))
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hcl : Nat.card (Subgroup.closure
      {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap}) = 4)
    (hclJ : Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap} ≤
      autI hV (thompsonJ T))
    (hW4 : Nat.card ↥(autI hV (T ⊓ K) ⊓ altOf L θ) = 4)
    (hTA : autI hV T ⊓ altOf L θ ≤ autI hV (T ⊓ K))
    (haltK : altOf L θ ≤ autI hV K)
    (hdec : autI hV (T ⊓ K) ≤ (autI hV (T ⊓ K) ⊓ altOf L θ) ⊔
      (autI hV (T ⊓ K) ⊓ Subgroup.centralizer (L : Set (MulAut (IntMod V hV)))))
    (hD : ∀ s ∈ thompsonJ T, ∀ t ∈ T ⊓ K, ⁅s, t⁆ ∈ D)
    (hDN : H ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer (D : Set G)) :
    autI hV (T ⊓ K) ⊓ altOf L θ ≤ autI hV D := by
  classical
  set P := T ⊓ K with hP
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHN
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs₁, hs₂⟩ := exists_two_swaps hcl
  have hclT : Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap} ≤
      autI hV T := (Subgroup.closure_le _).mpr fun x hx => hx.2.1
  have hgalt : elt L θ (swap a b * swap c d) ∈ altOf L θ := by
    refine elt_mem_altOf ?_
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    rfl
  have hgW : elt L θ (swap a b * swap c d) ∈ autI hV P ⊓ altOf L θ := by
    refine ⟨hTA ⟨?_, hgalt⟩, hgalt⟩
    rw [elt_mul]
    exact (autI hV T).mul_mem (hclT hs₁) (hclT hs₂)
  obtain ⟨hx₁W, hx₂W, hall⟩ :=
    fourGroup_of_card θ inf_le_right hW4 hab hac had hbc hbd hcd hgW
  obtain ⟨e1, e2, e3, -, -, -, -, -, -, -, -, -⟩ :=
    fourGroup_facts a b c d hab hac had hbc hbd hcd
  obtain ⟨e4, -⟩ := fourGroup_facts' a b c d hab hac had hbc hbd hcd
  obtain ⟨a₀, ha₀J, ha₀⟩ := (mem_autI hV).1 (hclJ hs₁)
  obtain ⟨t₁, ht₁P, ht₁⟩ := (mem_autI hV).1 hx₁W.1
  set c₀ : Subgroup.normalizer (V : Set G) := a₀ * t₁ * a₀⁻¹ * t₁⁻¹ with hc₀
  have hs₁inv : (elt L θ (swap a b))⁻¹ = elt L θ (swap a b) := by rw [← elt_inv, swap_inv]
  have hx₁inv : (elt L θ (swap a c * swap b d))⁻¹ = elt L θ (swap b d * swap a c) := by
    rw [← elt_inv, mul_inv_rev, swap_inv, swap_inv]
  have hc₀g : convI hV c₀ = elt L θ (swap a b * swap c d) := by
    rw [hc₀, map_mul, map_mul, map_mul, map_inv, map_inv, ha₀, ht₁, hs₁inv, hx₁inv, ← elt_mul,
      ← elt_mul, ← elt_mul, e3]
  have hc₀D : (c₀ : G) ∈ D := by
    have hcoe : (c₀ : G) = ⁅(a₀ : G), (t₁ : G)⁆ := rfl
    rw [hcoe]
    exact hD _ ha₀J _ ht₁P
  set ω := elt L θ (swap b c * swap c d) with hω
  have hωalt : ω ∈ altOf L θ := by
    refine elt_mem_altOf ?_
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hbc, Perm.sign_swap hcd]
    rfl
  have hωinv : ω⁻¹ = elt L θ (swap c d * swap b c) := by
    rw [hω, ← elt_inv, mul_inv_rev, swap_inv, swap_inv]
  have hconj : ∀ σ, ω * elt L θ σ * ω⁻¹ =
      elt L θ ((swap b c * swap c d) * σ * (swap c d * swap b c)) := by
    intro σ
    rw [hωinv, hω, ← elt_mul, ← elt_mul]
  have hωP : ∀ q ∈ autI hV P, ω * q * ω⁻¹ ∈ autI hV P := by
    intro q hq
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup (A := autI hV P ⊓ altOf L θ)
      (B := autI hV P ⊓ Subgroup.centralizer (L : Set (MulAut (IntMod V hV))))
      (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x (altOf_le hx.2)) (hdec hq)
    have hw'c : ω * w' = w' * ω := Subgroup.mem_centralizer_iff.mp hw'.2 _ (elt_mem _)
    have e : ω * (w * w') * ω⁻¹ = (ω * w * ω⁻¹) * w' := by
      calc ω * (w * w') * ω⁻¹ = ω * w * ω⁻¹ * (ω * w') * ω⁻¹ := by group
        _ = ω * w * ω⁻¹ * (w' * ω) * ω⁻¹ := by rw [hw'c]
        _ = (ω * w * ω⁻¹) * w' := by group
    rw [e]
    refine (autI hV P).mul_mem ?_ hw'.1
    rcases hall w hw with rfl | rfl | rfl | rfl
    · simp
    · rw [hconj, e1]
      exact hx₁W.1
    · rw [hconj, e2]
      exact hx₂W.1
    · rw [hconj, e4]
      exact hgW.1
  obtain ⟨z₀, hz₀K, hz₀⟩ := (mem_autI hV).1 (haltK hωalt)
  have hz : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K,
      p'⁻¹ * ((z₀ : G) * p * (z₀ : G)⁻¹) ∈ Subgroup.centralizer (V : Set G) := by
    intro p hp
    have hpN : p ∈ Subgroup.normalizer (V : Set G) := hKN hp.2
    have h1 : convI hV (z₀ * ⟨p, hpN⟩ * z₀⁻¹) ∈ autI hV P := by
      rw [map_mul, map_mul, map_inv, hz₀]
      exact hωP _ (convI_mem_autI hV hp hpN)
    obtain ⟨p', hp', hp'eq⟩ := (mem_autI hV).1 h1
    refine ⟨(p' : G), hp', ?_⟩
    have h2 : convI hV (p'⁻¹ * (z₀ * ⟨p, hpN⟩ * z₀⁻¹)) = 1 := by
      rw [map_mul, map_inv, hp'eq, inv_mul_cancel]
    exact (convI_eq_one_iff hV _).1 h2
  obtain ⟨p, hp, c', hc', y, hy, hz₀eq⟩ :=
    exists_eq_mul_normalizer hHN hT hKH hHK (hKH hz₀K) hz
  have hpN : p ∈ Subgroup.normalizer (V : Set G) := hTN hp.1
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := hHN hy.1
  have hc'N : c' ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hc'
  set z : Subgroup.normalizer (V : Set G) := ⟨p, hpN⟩ * ⟨y, hyN⟩ with hzdef
  have hzω : convI hV z = ω := by
    have e : z₀ = ⟨p, hpN⟩ * ⟨c', hc'N⟩ * ⟨y, hyN⟩ := Subtype.ext hz₀eq
    have hc1 : convI hV ⟨c', hc'N⟩ = 1 := (convI_eq_one_iff hV _).2 hc'
    rw [← hz₀, e, hzdef]
    simp only [map_mul, hc1, mul_one]
  have hzN : (z : G) ∈ H ⊓ Subgroup.normalizer (P : Set G) :=
    ⟨H.mul_mem (hT.1 hp.1) hy.1, Subgroup.mul_mem _ (Subgroup.le_normalizer hp) hy.2⟩
  have hmemD : ∀ u : Subgroup.normalizer (V : Set G),
      (u : G) ∈ H ⊓ Subgroup.normalizer (P : Set G) → convI hV (u * c₀ * u⁻¹) ∈ autI hV D := by
    intro u hu
    refine (mem_autI hV).2 ⟨u * c₀ * u⁻¹, ?_, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hDN hu) (c₀ : G)).mp hc₀D
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hgD : elt L θ (swap a b * swap c d) ∈ autI hV D := (mem_autI hV).2 ⟨c₀, hc₀D, hc₀g⟩
  have hx₁D : elt L θ (swap a c * swap b d) ∈ autI hV D := by
    have := hmemD z hzN
    rwa [map_mul, map_mul, map_inv, hzω, hc₀g, hconj, e1] at this
  have hx₂D : elt L θ (swap a d * swap b c) ∈ autI hV D := by
    have := hmemD (z * z) ⟨H.mul_mem hzN.1 hzN.1, Subgroup.mul_mem _ hzN.2 hzN.2⟩
    have e : ω * ω * elt L θ (swap a b * swap c d) * (ω * ω)⁻¹ =
        ω * (ω * elt L θ (swap a b * swap c d) * ω⁻¹) * ω⁻¹ := by group
    rwa [map_mul, map_mul, map_inv, map_mul, hzω, hc₀g, e, hconj, e1, hconj, e2] at this
  intro w hw
  rcases hall w hw with rfl | rfl | rfl | rfl
  · exact (autI hV D).one_mem
  · exact hgD
  · exact hx₁D
  · exact hx₂D

end PerComponent

section Main

variable {G : Type} [Group G] [Finite G]

theorem a5_gen {H T M₂ V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hmp : MinParabolic H T M₂) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hKJ : twoResidual H ≤ thompsonJ H)
    (I : Finset (Subgroup (MulAut (IntMod V hV))))
    (hcard : I.card = 1 ∨ I.card = 2)
    (hJI : autI hV (thompsonJ H) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hA5 : ∀ L ∈ I, E2.IsA5Module L)
    (h3 : autI hV (thompsonJ T) = ⨆ L ∈ I, (L ⊓ autI hV (thompsonJ T)) ∧
      ∀ L ∈ I, Nat.card ↥(L ⊓ autI hV (thompsonJ T)) = 4 ∧
        ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ autI hV (thompsonJ T) =
          Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap})
    (hDP : D ≤ T ⊓ twoResidual H)
    (hDN : H ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G) ≤
      Subgroup.normalizer (D : Set G))
    (hD : ∀ s ∈ thompsonJ T, ∀ t ∈ T ⊓ twoResidual H, ⁅s, t⁆ ∈ D) :
    T ⊓ twoResidual H ≤ D ⊔ pCoreOf 2 (twoResidual H) := by
  classical
  have _ := hA5
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  set K := twoResidual H with hKdef
  set P := T ⊓ K with hPdef
  have hTH : T ≤ H := hmp.isSylow.1
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hPsyl : IsSylowTwoOf P K := B6.isSylowTwoOf_inf_normal hmp.isSylow hKH hHK
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((B6.thompsonJ_le T).trans (hTH.trans h))
  have hQ : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H :=
    hmp.inf_centralizer_eq_pCoreOf hred hHV
  obtain ⟨-, hL4⟩ := h3
  choose θ hθ using fun L (hL : L ∈ I) => (hL4 L hL).2
  have hT2 : IsPGroup 2 T := hmp.isSylow.2.1
  obtain ⟨alt, halt_eq⟩ : ∃ alt : Subgroup (MulAut (IntMod V hV)) →
      Subgroup (MulAut (IntMod V hV)), ∀ L (hL : L ∈ I), alt L = altOf L (θ L hL) :=
    ⟨fun L => if hL : L ∈ I then altOf L (θ L hL) else L, fun L hL => dite_eq_left hL⟩
  have hIH : (⨆ L ∈ I, L) ≤ autI hV H := by
    rw [← hJI]
    exact autI_mono hV (thompsonJ_le_self H)
  have hLH : ∀ L ∈ I, L ≤ autI hV H := fun L hL =>
    (le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') L hL le_rfl).trans hIH
  have hAltK : ∀ L ∈ I, alt L ≤ autI hV K := fun L hL => by
    rw [halt_eq L hL]
    exact altOf_le_of_odd fun x hx hodd => E2.mem_autI_twoResidual_of_odd (hLH L hL hx) hodd
  have hLalt : ∀ L ∈ I, alt L ≤ L ∧ L ≤ Subgroup.normalizer (alt L : Set _) ∧
      Nat.card (alt L) = 60 := fun L hL => by
    rw [halt_eq L hL]
    exact ⟨altOf_le, le_normalizer_altOf, card_altOf⟩
  have hsqL : ∀ L ∈ I, ∀ x ∈ L, x * x ∈ alt L := fun L hL x hx => by
    rw [halt_eq L hL]
    exact mul_self_mem_altOf hx
  have hKD : autI hV K = ⨆ L ∈ I, alt L := by
    refine le_antisymm ?_ (iSup₂_le hAltK)
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hφ
    have hKD' : K ≤ ((⨆ L ∈ I, alt L).comap (convI hV)).map
        (Subgroup.normalizer (V : Set G)).subtype := by
      rw [hKdef, F6.twoResidual_eq_oTwoUpper, oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hxH, hxo⟩
      refine ⟨⟨x, hHN hxH⟩, ?_, rfl⟩
      show convI hV ⟨x, hHN hxH⟩ ∈ ⨆ L ∈ I, alt L
      apply odd_mem_iSup_alt hcard hcomm hsqL
      · rw [← hJI]
        exact convI_mem_autI hV (hKJ (F6.mem_twoResidual_of_odd hxH hxo)) _
      · have h1 := orderOf_map_dvd (convI hV) ⟨x, hHN hxH⟩
        rw [Subgroup.orderOf_mk] at h1
        exact hxo.of_dvd_nat h1
    obtain ⟨n, hn, hng⟩ := hKD' hgK
    have e : n = g := Subtype.ext hng
    rw [← e]
    exact hn
  have hPsylK : IsSylowTwoOf (autI hV P) (autI hV K) := B2F.isSylowTwoOf_autI hV hKN hPsyl
  obtain ⟨hP4, hPdec⟩ := sylow_decomp hcard hcomm hind hLalt (hKD ▸ hPsylK)
  have hPT : autI hV P = autI hV T ⊓ autI hV K :=
    F1.eq_of_isSylowTwoOf_le hPsylK inf_le_right
      ((B2F.isPGroup_autI hV hT2 hTN).to_le inf_le_left)
      (le_inf (autI_mono hV inf_le_left) (autI_mono hV inf_le_right))
  have hWT : ∀ L ∈ I, autI hV T ⊓ alt L = autI hV P ⊓ alt L := fun L hL => by
    rw [hPT, inf_assoc, inf_eq_right.mpr (hAltK L hL)]
  have hdecL : ∀ L ∈ I, autI hV P ≤ (autI hV P ⊓ alt L) ⊔
      (autI hV P ⊓ Subgroup.centralizer (L : Set (MulAut (IntMod V hV)))) := by
    intro L hL
    refine hPdec.le.trans (iSup₂_le fun L' hL' => ?_)
    by_cases hLL : L' = L
    · rw [hLL]
      exact le_sup_left
    · refine le_sup_of_le_right (le_inf inf_le_left fun u hu => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hcomm L hL L' hL' (Ne.symm hLL) h hh u ((hLalt L' hL').1 hu.2)
  have hWD : ∀ L ∈ I, autI hV P ⊓ alt L ≤ autI hV D := by
    intro L hL
    have hcl : Nat.card (Subgroup.closure
        {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ L hL ⟨x, hx⟩).IsSwap}) = 4 := by
      rw [← hθ L hL]
      exact (hL4 L hL).1
    have hclJ : Subgroup.closure
        {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ L hL ⟨x, hx⟩).IsSwap} ≤
          autI hV (thompsonJ T) := by
      rw [← hθ L hL]
      exact inf_le_right
    have hW4 := hP4 L hL
    rw [halt_eq L hL] at hW4
    have hTA : autI hV T ⊓ altOf L (θ L hL) ≤ autI hV P := by
      rw [← halt_eq L hL, hWT L hL]
      exact inf_le_left
    have haltK : altOf L (θ L hL) ≤ autI hV K := by
      rw [← halt_eq L hL]
      exact hAltK L hL
    have hdec := hdecL L hL
    rw [halt_eq L hL] at hdec ⊢
    exact a5Gen_fourGroup_le_autI hV (θ L hL) hHN hmp.isSylow hKH hHK hcl hclJ hW4 hTA
      haltK hdec hD hDN
  have hPD : autI hV P ≤ autI hV D := hPdec.le.trans (iSup₂_le hWD)
  have hPCK : P ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K := by
    have h1 : P ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H ⊓ K := by
      rw [← hQ, hPdef, inf_right_comm]
    rw [h1]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk), hHK (hKH hk)⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  intro t ht
  have htN : t ∈ Subgroup.normalizer (V : Set G) := hTN ht.1
  obtain ⟨x, hxD, hx⟩ := (mem_autI hV).1 (hPD (convI_mem_autI hV ht htN))
  have hxP : (x : G) ∈ P := hDP hxD
  have hxt : (x : G)⁻¹ * t ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : convI hV (x⁻¹ * ⟨t, htN⟩) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
    exact (convI_eq_one_iff hV _).1 h1
  have hxtO : (x : G)⁻¹ * t ∈ pCoreOf 2 K := hPCK ⟨P.mul_mem (P.inv_mem hxP) ht, hxt⟩
  have e : t = (x : G) * ((x : G)⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hxD hxtO

end Main

end CFSG.Quasithin.Ch3g316
