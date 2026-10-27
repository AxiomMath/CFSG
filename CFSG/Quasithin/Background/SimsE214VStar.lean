module

public import CFSG.Quasithin.Background.SimsE214TwoSix
public import CFSG.Quasithin.Background.SimsE214TwoSp4
public import CFSG.Quasithin.Background.SimsE213M

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214T

variable {G : Type} [Group G] [Finite G]

theorem star_eq_center_of_six {T M V I : Subgroup G} {g : G}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (e : E2.StarQuot (M ⊓ I) I ≃* Equiv.Perm (Fin 6)) :
    E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (E2.StarQuot (M ⊓ I) I) := e.toEquiv.nontrivial
  set Vs := E2.star (M ⊓ I) I V with hVs
  have hVT : Vs ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hZ4 : Nat.card ↥(centerOf (E2.star (M ⊓ I) I (T ⊓ I))) ≤ 4 :=
    E213M.card_le_of_le_centralizer (k := 1) (Or.inr ⟨rfl, ⟨e⟩⟩)
      (E2.isSylowTwoOf_star_inf (M := M) hp.sylow) inf_le_left inf_le_right
  have hsq : ∀ v ∈ Vs, v * v = 1 := fun v hv => E2.sq_eq_one_of_mem_star hp.elem hv
  have hV2 : IsPGroup 2 Vs := fun x =>
    ⟨1, Subtype.ext (by
      rw [SubmonoidClass.coe_pow, pow_one, pow_two, OneMemClass.coe_one]
      exact hsq _ x.2)⟩
  have hV1 : Nat.card Vs ≠ 1 := fun h1 =>
    E2.star_ne_bot_of_gen (M' := M ⊓ I) hp.mem hp.gen (Subgroup.card_eq_one.mp h1)
  have htop : Vs ⊔ Vs.map (MulAut.conj (E2P.starMap (M ⊓ I) I ⟨g, hp.mem⟩)).toMonoidHom = ⊤ := by
    have h1 : E2.star (M ⊓ I) I (V ⊔ B6.conjSub g V) = ⊤ := by
      rw [← hp.gen]
      exact E2P.star_top (M ⊓ I) I
    rw [E2.star_sup hp.V_le hp.conj_le, E2.star_conjSub hp.mem] at h1
    exact h1
  have hVne2 : Nat.card Vs ≠ 2 := by
    intro h2
    apply not_comm_commutator_perm_six
    have hmapc : (commutator (E2.StarQuot (M ⊓ I) I)).map e.toMonoidHom =
        commutator (Equiv.Perm (Fin 6)) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    intro x hx y hy
    rw [← hmapc] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, comm_of_card_two h2 hsq htop hx' hy']
  have hV4 : 4 ≤ Nat.card Vs := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV2
    rw [hn] at hV1 hVne2 ⊢
    rcases n with _ | _ | n
    · exact absurd rfl hV1
    · exact absurd rfl hVne2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Subgroup.eq_of_le_of_card_ge (le_inf hVT hVZ) (hZ4.trans hV4)

theorem star_eq_center_of_member {H T M V I : Subgroup G} {g : G}
    (h : E2.Hyp28 H T M V) (hTI : IsTISetIn V M) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥) :
    E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) := by
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  have hZ' : V ⊓ B6.conjSub g⁻¹ V ≠ ⊥ := e ▸ hZ
  have hI' := E213M.noRoot_of_isInIHTV hI
  have hp := h.pair_of_member hI' (I.inv_mem hg) hgen
  have hVZ := E2.e2_11_two h hI' hp.V_le
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G) :=
    (E2.inf_eq_inf_normalizer_of_central hTI (hp.normalizer_le.trans inf_le_left) hZ'
      inf_le_left fun z hz x hx => hp.mem_center hz hx).le.trans inf_le_right
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  obtain ⟨-, -, hsyl, -, k, -, hcase⟩ := hI
  rcases hcase with ⟨hk, hY, hBor⟩ | ⟨-, p, a, hp', hp2, -, ⟨d⟩⟩ | ⟨-, -, hY, hBor, -, hroot⟩
  ·
    exact (star_eq_and_comm hp hsyl hTMI (I.inv_mem hg) hgen hVZ hMN hBor (by omega) hY).1
  ·
    exact (E2.star_eq_center_of_dihedral hp hsyl hVZ (hp'.odd_of_ne_two hp2).pow d).2
  ·
    rcases hY with hY | ⟨-, ⟨e6⟩⟩
    · exact (star_eq_center_of_sp4 hp hsyl hTMI (I.inv_mem hg) hgen hVZ hMN hBor hroot hY).1
    · exact star_eq_center_of_six hp hVZ e6

end E214T

theorem e214_vstar_sp4
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (_hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI TI JI B A P Z : Subgroup Γ) (k : ℕ) (hMI : MI = M ⊓ I) (hTI' : TI = T ⊓ I)
    (_hJI : JI = kerIn MI I) (_hB : B = V ⊓ pCoreOf 2 I)
    (_hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) (_hP : P = A ⊔ B)
    (_hZdef : Z = V ⊓ conjSubgroup V g)
    (_hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞)) :
    IsSp4Full k (E2.StarQuot MI I) → E2.star MI I V = centerOf (E2.star MI I TI) := by
  subst hMI hTI'
  exact fun _ => E214T.star_eq_center_of_member h hTI hI hg hIV hZ

end CFSG.Quasithin.SimsE2
