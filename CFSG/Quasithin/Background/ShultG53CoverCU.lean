module

public import CFSG.Quasithin.Background.ShultG53CoverCT
public import CFSG.Quasithin.Background.ShultG53CoverBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

theorem closure_orbit_inv {X : Type} [Group X] (W : Md X) (w : W.carrier) (g : X)
    {s : W.carrier} (hs : s ∈ AddSubgroup.closure (Set.range fun g : X => W.ρ g w)) :
    W.ρ g s ∈ AddSubgroup.closure (Set.range fun g : X => W.ρ g w) := by
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g', rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨g * g', ?_⟩
    show W.ρ (g * g') w = W.ρ g (W.ρ g' w)
    rw [map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx


theorem mul_mem_Hx {k : Fin 2} {h h' : ↥(alternatingGroup (Fin 6))} (hh : h ∈ Hx k)
    (hh' : h' ∈ Hx k) : h * h' ∈ Hx k := by
  have e : ρk k h (x0 k) = x0 k := hh
  have e' : ρk k h' (x0 k) = x0 k := hh'
  show ρk k (h * h') (x0 k) = x0 k
  rw [map_mul, Module.End.mul_apply, e', e]

theorem orbit_x0_span (k : Fin 2) :
    AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => ρk k g (x0 k)) = ⊤ := by
  rcases ρk_irred k (AddSubgroup.closure
      (Set.range fun g : ↥(alternatingGroup (Fin 6)) => ρk k g (x0 k)))
      (fun g m hm => closure_orbit_inv (Mk k) (x0 k) g hm) with h | h
  · exfalso
    have : x0 k ∈ AddSubgroup.closure
        (Set.range fun g : ↥(alternatingGroup (Fin 6)) => ρk k g (x0 k)) :=
      AddSubgroup.subset_closure ⟨1, by show ρk k 1 (x0 k) = x0 k; rw [map_one,
        Module.End.one_apply]⟩
    rw [h, AddSubgroup.mem_bot] at this
    exact x0_ne_zero k this
  · exact h

theorem Phi_surj_N0 (k : Fin 2) (v : V4) : ∃ y : ↥(Nk k 0), Phi (y : Fn) = v := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_ab v
  exact ⟨⟨(Pi.single a 1 + Pi.single b 1 : Fn), two_single_mem k a b ha hb⟩,
    phi_two_single a b v hab⟩

theorem exists_good_vector (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6)))
    (hW : W.IsCovering (Mk k)) : ∃ w : W.carrier, (∀ h ∈ Hx k, W.ρ h w = w) ∧
      AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) = ⊤ ∧
      w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0 := by
  obtain ⟨hperf, W₀, f, hfix, hsurj, hker, heq⟩ := hW
  obtain ⟨yh, hyh⟩ := hsurj (y0P k)
  obtain ⟨w', hw'⟩ : ∃ w' : W.carrier, w' = W.ρ (tE k) yh + yh := ⟨_, rfl⟩
  have hfw' : f w' = x0 k := by
    rw [hw', map_add, heq, hyh]
    exact ρk_tE_y0 k
  have htw' : W.ρ (tE k) w' = w' := by
    rw [hw', map_add, ← Module.End.mul_apply, ← map_mul, tE_sq, map_one, Module.End.one_apply,
      add_comm]
  have hcW0 : ∀ h ∈ Hx k, W.ρ h w' - w' ∈ W₀ := by
    intro h hh
    have hh' : ρk k h (x0 k) = x0 k := hh
    rw [← hker, map_sub, heq, hfw']
    show ρk k h (x0 k) - x0 k = 0
    rw [hh', sub_self]
  have hadd : ∀ h ∈ Hx k, ∀ h' ∈ Hx k,
      W.ρ (h * h') w' - w' = (W.ρ h w' - w') + (W.ρ h' w' - w') := by
    intro h hh h' hh'
    have hz : W.ρ h (W.ρ h' w' - w') = W.ρ h' w' - w' := hfix _ (hcW0 h' hh') h
    have e : W.ρ h (W.ρ h' w') = (W.ρ h' w' - w') + W.ρ h w' := by
      have e1 : W.ρ h' w' = (W.ρ h' w' - w') + w' := by abel
      calc W.ρ h (W.ρ h' w') = W.ρ h ((W.ρ h' w' - w') + w') := by rw [← e1]
        _ = W.ρ h (W.ρ h' w' - w') + W.ρ h w' := map_add _ _ _
        _ = (W.ρ h' w' - w') + W.ρ h w' := by rw [hz]
    rw [map_mul, Module.End.mul_apply, e]
    abel
  have hc_one : ∀ a : Fin 9, W.ρ (L3E k a) w' = w' := by
    intro a
    have ha : L3E k a ∈ Hx k := ρk_L3E k a
    have h2 : L3E k a * L3E k a ∈ Hx k := mul_mem_Hx ha ha
    have h3 := hadd _ h2 _ ha
    rw [L3E_cube, map_one, Module.End.one_apply, sub_self, hadd _ ha _ ha, add_self_zmod2,
      zero_add] at h3
    exact sub_eq_zero.mp h3.symm
  have hfix_w' : ∀ h ∈ Hx k, W.ρ h w' = w' := by
    intro h hh
    obtain ⟨a, b, h' | h'⟩ := Hx_decomp k hh
    · rw [h', map_mul, Module.End.mul_apply, hc_one b, hc_one a]
    · rw [h', map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, hc_one b, hc_one a,
        htw']
  obtain ⟨z, hz⟩ : ∃ z : W.carrier,
      z = w' + W.ρ (h0E k) w' + W.ρ (h0E k) (W.ρ (h0E k) w') := ⟨_, rfl⟩
  have hfz : f z = 0 := by
    rw [hz]
    simp only [map_add, heq, hfw']
    show x0 k + ρk k (h0E k) (x0 k) + ρk k (h0E k) (ρk k (h0E k) (x0 k)) = 0
    rw [ρk_h0E_x0, ρk_h0E_y2]
    exact (points_aux k).2.2.2.2.2.2
  have hzW0 : z ∈ W₀ := (hker z).mp hfz
  refine ⟨w' + z, ?_, ?_, ?_⟩
  · intro h hh
    rw [map_add, hfix_w' h hh, hfix z hzW0 h]
  · have hfw : f (w' + z) = x0 k := by rw [map_add, hfw', hfz, add_zero]
    have himg : ∀ m : V4, ∃ s ∈ AddSubgroup.closure
        (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g (w' + z)), f s = m := by
      have hmap : (AddSubgroup.closure
          (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g (w' + z))).map f = ⊤ := by
        apply top_unique
        rw [← orbit_x0_span k, AddSubgroup.closure_le]
        rintro _ ⟨g, rfl⟩
        refine ⟨W.ρ g (w' + z), AddSubgroup.subset_closure ⟨g, rfl⟩, ?_⟩
        rw [heq, hfw]
      intro m
      have hm : m ∈ (AddSubgroup.closure
          (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g (w' + z))).map f := by
        rw [hmap]
        exact AddSubgroup.mem_top m
      obtain ⟨s, hs, hsm⟩ := hm
      exact ⟨s, hs, hsm⟩
    apply top_unique
    rw [← hperf, AddSubgroup.closure_le]
    rintro _ ⟨g, m, rfl⟩
    obtain ⟨s, hs, hfs⟩ := himg (f m)
    have hmz : m - s ∈ W₀ := (hker _).mp (by rw [map_sub, hfs, sub_self])
    have h1 : W.ρ g (m - s) = m - s := hfix _ hmz g
    have h2 : W.ρ g m - m = W.ρ g s - s := by
      rw [map_sub] at h1
      calc W.ρ g m - m = (W.ρ g m - W.ρ g s) - (m - s) + (W.ρ g s - s) := by abel
        _ = W.ρ g s - s := by rw [h1, sub_self, zero_add]
    show W.ρ g m - m ∈ AddSubgroup.closure
      (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g (w' + z))
    rw [h2]
    exact AddSubgroup.sub_mem _ (closure_orbit_inv W (w' + z) g hs) hs
  · have e1 : W.ρ (h0E k) (w' + z) = W.ρ (h0E k) w' + z := by rw [map_add, hfix z hzW0]
    have e2 : W.ρ (h0E k) (W.ρ (h0E k) (w' + z)) = W.ρ (h0E k) (W.ρ (h0E k) w') + z := by
      rw [e1, map_add, hfix z hzW0]
    rw [e2, e1]
    have e3 : w' + z + (W.ρ (h0E k) w' + z) + (W.ρ (h0E k) (W.ρ (h0E k) w') + z) =
        (w' + W.ρ (h0E k) w' + W.ρ (h0E k) (W.ρ (h0E k) w')) + (z + z + z) := by abel
    rw [e3, ← hz]
    have e4 : z + (z + z + z) = (z + z) + (z + z) := by abel
    rw [e4]
    exact add_self_zmod2 _

theorem perfect_aux (k : Fin 2) (C : Md ↥(alternatingGroup (Fin 6)))
    (π : ↥(Nk k 0) →+ C.carrier) (hs : Function.Surjective π)
    (hk : ∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
      π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n))
    (D : AddSubgroup C.carrier) (hDinv : ∀ (g : ↥(alternatingGroup (Fin 6))) (d : C.carrier),
      d ∈ D → C.ρ g d ∈ D)
    (hDgen : ∀ (g : ↥(alternatingGroup (Fin 6))) (c : C.carrier), C.ρ g c - c ∈ D) : D = ⊤ := by
  let P : AddSubgroup Fn := (D.comap π).map (Nk k 0).subtype
  have hPmem : ∀ y : ↥(Nk k 0), (y : Fn) ∈ P ↔ π y ∈ D := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hP0 : P ≤ Nk k 0 := AddSubgroup.map_subtype_le _
  have hPinv : InvSub (permAct (Mk k)) P := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : π ⟨permAct (Mk k) g y, N0_inv k g y y.2⟩ ∈ D := by
      rw [he]
      exact hDinv g _ hy
    exact (hPmem ⟨permAct (Mk k) g y, N0_inv k g y y.2⟩).mpr h1
  have hN2P : Nk k 2 ≤ P := by
    intro x hx
    have hx0 : x ∈ Nk k 0 := N1_le_N0 k (N2_le_N1 k hx)
    refine (hPmem ⟨x, hx0⟩).mpr ?_
    rw [(hk ⟨x, hx0⟩).mpr hx]
    exact D.zero_mem
  have nontriv : P ≤ Nk k 1 → False := by
    intro hP1
    have hall : ∀ (g : ↥(alternatingGroup (Fin 6))) (v : V4), ρk k g v = v := by
      intro g v
      obtain ⟨y, hy⟩ := Phi_surj_N0 k v
      have hx0 : permAct (Mk k) g y - y ∈ Nk k 0 := (Nk k 0).sub_mem (N0_inv k g y y.2) y.2
      have hxP : permAct (Mk k) g y - y ∈ P := by
        refine (hPmem ⟨permAct (Mk k) g y - y, hx0⟩).mpr ?_
        have e : (⟨permAct (Mk k) g y - y, hx0⟩ : ↥(Nk k 0)) =
            ⟨permAct (Mk k) g y, N0_inv k g y y.2⟩ - y := Subtype.ext rfl
        rw [e, map_sub, he]
        exact hDgen g (π y)
      have h1 : permAct (Mk k) g y - y ∈ Nk k 1 := hP1 hxP
      have h2 : Phi (permAct (Mk k) g y - y) = 0 :=
        AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp h1).2
      rw [map_sub, phi_equiv, hy, sub_eq_zero] at h2
      exact h2
    have h1 := hall (tE k) (y0P k)
    have h2 := ρk_tE_y0 k
    rw [h1, add_self_zmod2] at h2
    exact x0_ne_zero k h2.symm
  obtain ⟨n, hn5, hPn⟩ := eq_chain_of_invSub (Nk k) (chain_isTop k) (Nk_five k) hPinv hP0
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [eq_top_iff]
    intro c _
    obtain ⟨y, rfl⟩ := hs c
    exact (hPmem y).mp (by rw [hPn]; exact y.2)
  · exact (nontriv hPn.le).elim
  · exact (nontriv (hPn.le.trans (N2_le_N1 k))).elim
  · exfalso
    have h := AddSubgroup.card_le_of_le (show Nk k 2 ≤ Nk k 3 from hPn ▸ hN2P)
    rw [card_N2, card_N3] at h
    norm_num at h
  · exfalso
    have h := AddSubgroup.card_le_of_le (show Nk k 2 ≤ Nk k 4 from hPn ▸ hN2P)
    rw [card_N2, card_N4] at h
    norm_num at h
  · exfalso
    have h := AddSubgroup.card_le_of_le (show Nk k 2 ≤ Nk k 5 from hPn ▸ hN2P)
    rw [card_N2, Nk_five, AddSubgroup.card_bot] at h
    norm_num at h

theorem covering_of_quot (k : Fin 2) (C : Md ↥(alternatingGroup (Fin 6)))
    (π : ↥(Nk k 0) →+ C.carrier) (hs : Function.Surjective π)
    (hk : ∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
      π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n)) : C.IsCovering (Mk k) := by
  have hperf : C.IsPerfect := by
    unfold Md.IsPerfect
    refine perfect_aux k C π hs hk he _ ?_ ?_
    · intro g d hd
      induction hd using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g', m, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨g * g' * g⁻¹, C.ρ g m, ?_⟩
        have : C.ρ (g * g' * g⁻¹) (C.ρ g m) = C.ρ g (C.ρ g' m) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul,
            Module.End.mul_apply]
        rw [map_sub, this]
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    · intro g c
      exact AddSubgroup.subset_closure ⟨g, c, rfl⟩
  obtain ⟨f, hf⟩ := exists_lift π hs ((Phi).comp (Nk k 0).subtype) (fun n hn => by
    have h := (hk n).mp hn
    exact AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp (AddSubgroup.mem_inf.mp h).1).2)
  refine ⟨hperf, f.ker, f, ?_, ?_, ?_, ?_⟩
  · intro c hc g
    have hfc : f c = 0 := AddMonoidHom.mem_ker.mp hc
    obtain ⟨n, rfl⟩ := hs c
    rw [hf] at hfc
    have hfc' : Phi (n : Fn) = 0 := hfc
    have hx0 : permAct (Mk k) g (n : Fn) - n ∈ Nk k 0 :=
      (Nk k 0).sub_mem (N0_inv k g n n.2) n.2
    have hx2 : permAct (Mk k) g (n : Fn) - n ∈ Nk k 2 := by
      refine AddSubgroup.mem_inf.mpr ⟨AddSubgroup.mem_inf.mpr ⟨hx0, ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, map_sub, phi_equiv, hfc', map_zero, sub_zero]
      · obtain ⟨m, hm⟩ := psi1_law k g n
        rw [AddMonoidHom.mem_ker, map_sub, hm, hfc']
        simp [B0]
    have h := (hk ⟨permAct (Mk k) g (n : Fn) - n, hx0⟩).mpr hx2
    have e : (⟨permAct (Mk k) g (n : Fn) - n, hx0⟩ : ↥(Nk k 0)) =
        ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ - n := Subtype.ext rfl
    rw [e, map_sub, he, sub_eq_zero] at h
    exact h
  · intro v
    obtain ⟨y, hy⟩ := Phi_surj_N0 k v
    exact ⟨π y, by rw [hf]; exact hy⟩
  · intro c
    exact AddMonoidHom.mem_ker
  · intro g c
    obtain ⟨n, rfl⟩ := hs c
    rw [← he, hf, hf]
    exact phi_equiv k g n

theorem univ_of_quot (k : Fin 2) (C : Md ↥(alternatingGroup (Fin 6)))
    (π : ↥(Nk k 0) →+ C.carrier) (hs : Function.Surjective π)
    (hk : ∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
      π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n))
    (W : Md ↥(alternatingGroup (Fin 6))) (hW : W.IsCovering (Mk k)) :
    ∃ π' : C.carrier →+ W.carrier, Function.Surjective π' ∧
      ∀ (g : ↥(alternatingGroup (Fin 6))) (c : C.carrier), π' (C.ρ g c) = W.ρ g (π' c) := by
  obtain ⟨w, hHx, hgen, hrel⟩ := exists_good_vector k W hW
  obtain ⟨ψ, hψs, hψe, hψ0⟩ := cover_core k W w hHx hgen hrel
  obtain ⟨π', hπ'⟩ := exists_lift π hs ψ (fun n hn => hψ0 n ((hk n).mp hn))
  refine ⟨π', ?_, ?_⟩
  · intro v
    obtain ⟨n, rfl⟩ := hψs v
    exact ⟨π n, hπ' n⟩
  · intro g c
    obtain ⟨n, rfl⟩ := hs c
    rw [← he, hπ', hπ', hψe]

theorem card_of_quot (k : Fin 2) (C : Md ↥(alternatingGroup (Fin 6)))
    (π : ↥(Nk k 0) →+ C.carrier) (hs : Function.Surjective π)
    (hk : ∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2) : Nat.card C.carrier = 2 ^ 5 := by
  have h := card_eq_mul_of_quot (N := Nk k 0) (K := Nk k 2) ((N2_le_N1 k).trans (N1_le_N0 k))
    π hs hk
  rw [card_N0, card_N2] at h
  have h2 : (2 : ℕ) ^ 14 = 2 ^ 9 * 2 ^ 5 := by norm_num
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm

theorem isFiveDimCover_of_quot (k : Fin 2) (C : Md ↥(alternatingGroup (Fin 6)))
    (π : ↥(Nk k 0) →+ C.carrier) (hs : Function.Surjective π)
    (hk : ∀ n : ↥(Nk k 0), π n = 0 ↔ (n : Fn) ∈ Nk k 2)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
      π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = C.ρ g (π n)) : C.IsFiveDimCover (Mk k) :=
  ⟨⟨covering_of_quot k C π hs hk he, fun W hW => univ_of_quot k C π hs hk he W hW⟩,
    card_of_quot k C π hs hk⟩

end CFSG.Quasithin.ShultG53
