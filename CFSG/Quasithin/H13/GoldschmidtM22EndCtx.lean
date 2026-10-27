module

public import CFSG.Quasithin.Vol2.Ch6StatementsSec2
public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G]

abbrev HH (T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

abbrev UU (T L V : Subgroup G) : Subgroup G := conjClosure (ch6ZS T L V) (HH T)

abbrev KK (T V : Subgroup G) : Subgroup G := conjClosure V (HH T)

abbrev CHU (T L V : Subgroup G) : Subgroup G :=
  centralizerMod (quasithinOmegaOneCenter T) (HH T) (UU T L V)

variable [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem omegaOneCenter_le_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, -⟩
  exact (Subgroup.mem_inf.mp hx).2

omit [Finite G] in
theorem T_le_HH (T : Subgroup G) : T ≤ HH T := by
  intro t ht
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_centralizer T hz)) t ht).symm

theorem Z_le_V (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    quasithinOmegaOneCenter T ≤ V := by
  have hne := inf_omegaOneCenter_ne_bot h.sylow.1 h.toHyp611.isElemAbelian h.toHyp611.le_T
    h.toHyp611.T_le_normalizer h.toHyp611.ne_bot
  set Z := quasithinOmegaOneCenter T with hZdef
  have hdvd : Nat.card ↥(V ⊓ Z) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le inf_le_right
  have h1 : Nat.card ↥(V ⊓ Z) ≠ 1 := fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1)
  have h2 : Nat.card ↥(V ⊓ Z) = 2 := ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left h1
  have : V ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hZ])
  exact this ▸ inf_le_left

theorem Z_le_ZS (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    quasithinOmegaOneCenter T ≤ ch6ZS T L V :=
  le_inf (Z_le_V h hZ) ((omegaOneCenter_le_centralizer T).trans
    (Subgroup.centralizer_le (by exact_mod_cast (inf_le_left : T ⊓ L ≤ T))))

theorem V_le_HH (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    V ≤ HH T := by
  intro v hv
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (B2F.isElemAbelian_comm h.toHyp611.isElemAbelian (Z_le_V h hZ hz) hv)

theorem ZS_le_HH (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    ch6ZS T L V ≤ HH T :=
  inf_le_left.trans (V_le_HH h hZ)

theorem Z_le_UU (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    quasithinOmegaOneCenter T ≤ UU T L V :=
  (Z_le_ZS h hZ).trans (le_conjClosure _ _)

theorem UU_le_HH (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    UU T L V ≤ HH T :=
  conjClosure_le fun x hx z hz => (HH T).mul_mem ((HH T).mul_mem hx (ZS_le_HH h hZ hz))
    ((HH T).inv_mem hx)

omit [Finite G] in
theorem HH_le_normalizer_Z (T : Subgroup G) :
    HH T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.centralizer_le_normalizer _

omit [Finite G] in
theorem HH_le_normalizer_UU (T L V : Subgroup G) :
    HH T ≤ Subgroup.normalizer (UU T L V : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] in
theorem Z_central (T : Subgroup G) {x z : G} (hx : x ∈ HH T) (hz : z ∈ quasithinOmegaOneCenter T) :
    x * z = z * x :=
  (Subgroup.mem_centralizer_iff.mp hx z hz).symm

section Parts

variable (h : Hyp6Sec2 G T M L V)
include h

theorem UU_le_pCore (h6210 : Stmt6_2_10) : UU T L V ≤ pCoreOf 2 (HH T) :=
  (h6210 G T M L V h).1.2.1

theorem commutator_UU_le (h6210 : Stmt6_2_10) :
    ⁅UU T L V, pCoreOf 2 (HH T)⁆ ≤ quasithinOmegaOneCenter T :=
  (h6210 G T M L V h).1.2.2

theorem CHU_le_normalizer_V (h6210 : Stmt6_2_10) :
    CHU T L V ≤ Subgroup.normalizer (V : Set G) :=
  (h6210 G T M L V h).2.1.1

theorem isO2Trivial_CHU (h6210 : Stmt6_2_10) : IsO2Trivial (HH T) (CHU T L V) :=
  (h6210 G T M L V h).2.2.1

theorem not_V_le_CHU (h6210 : Stmt6_2_10) : ¬ V ≤ CHU T L V :=
  (h6210 G T M L V h).2.2.2.1

theorem commutator_V_UU_le (h6210 : Stmt6_2_10) : ⁅V, UU T L V⁆ ≤ V ⊓ UU T L V :=
  (h6210 G T M L V h).2.2.2.2

theorem relIndex_V_CHU (h6211 : Stmt6_2_11) : (V ⊓ CHU T L V).relIndex V = 2 :=
  h6211 G T M L V h

theorem HH_inf_normalizer_ZS_le (h629 : Stmt6_2_9) :
    HH T ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
  (h629 G T M L V h).2.1.symm.le.trans inf_le_right

end Parts

end CFSG.Quasithin.H13.GM22
