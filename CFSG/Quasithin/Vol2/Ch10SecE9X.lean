module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.Vol2.Ch10SecB3L32
public import CFSG.Quasithin.Vol2.Ch10SecE9H

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_omega (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter R : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (R : Set G), ∀ w ∈ quasithinOmegaOneCenter R,
      m * w * m⁻¹ ∈ quasithinOmegaOneCenter R := by
    intro m hm w hw
    have hle : quasithinOmegaOneCenter R ≤
        (quasithinOmegaOneCenter R).comap (MulAut.conj m).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      obtain ⟨⟨hzR, hzC⟩, hz2⟩ := hz
      have hc : m * z * m⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hr' : m⁻¹ * r * m ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) r).mp hr
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hzC _ hr'
        calc r * (m * z * m⁻¹) = m * ((m⁻¹ * r * m) * z) * m⁻¹ := by group
          _ = m * (z * (m⁻¹ * r * m)) * m⁻¹ := by rw [h1]
          _ = m * z * m⁻¹ * r := by group
      have h2 : (m * z * m⁻¹) ^ 2 = 1 := by
        rw [sq, show m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ by group, ← sq, hz2]
        group
      exact Subgroup.subset_closure
        (show m * z * m⁻¹ ∈ {z | z ∈ R ⊓ Subgroup.centralizer (R : Set G) ∧ z ^ 2 = 1} from
          ⟨⟨(Subgroup.mem_normalizer_iff.mp hm z).mp hzR, hc⟩, h2⟩)
    exact hle hw
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key n hn w, fun hw => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hw
  convert this using 1
  group

variable [Finite G]

theorem conjClosure_le_centralizer {T₁ P T W : Subgroup G} (hTP : IsSylowTwoOf T P)
    (hX : oTwoUpper P ≤ Subgroup.centralizer (W : Set G))
    (hT : T ≤ Subgroup.normalizer (W : Set G))
    (hN : Subgroup.normalizer (T₁ : Set G) ≤ Subgroup.normalizer (W : Set G)) :
    conjClosure (oTwoUpper P) (Subgroup.normalizer (T₁ : Set G) ⊔ P) ≤
      Subgroup.centralizer (W : Set G) := by
  have hXN : oTwoUpper P ≤ Subgroup.normalizer (W : Set G) := fun x hx =>
    E9.mem_normalizer_of_mem_centralizer (hX hx)
  have hPW : P ≤ Subgroup.normalizer (W : Set G) :=
    (C10P34.le_oTwoUpper_sup hTP).trans (sup_le hXN hT)
  have hG₀ : Subgroup.normalizer (T₁ : Set G) ⊔ P ≤ Subgroup.normalizer (W : Set G) :=
    sup_le hN hPW
  refine conjClosure_le fun g hg x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hgw : g⁻¹ * w * g ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hG₀ hg)) w).mp hw
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp (hX hx) _ hgw
  calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * w := by group

variable {T L I : Subgroup G}

theorem le_fsuM_of_le_centralizer (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (hne : fsuCVM T L I ≠ ⊥)
    {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter (T1 T L) : Set G)) :
    K ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCT : fsuCVM T L I ≤ T := inf_le_left.trans (SecA.fsuVM_le_T hyp)
  have hTn : T ≤ Subgroup.normalizer (fsuCVM T L I : Set G) :=
    (SecA.le_fsuM T L).trans (SecA.le_normalizer_fsuCVM T L I)
  obtain ⟨u, huC, hu1, huT⟩ := SecA.exists_ne_one_mem_centralizer hyp.fsu.sylow.1 hCT hTn hne
  obtain ⟨hcomm, helem, -⟩ := hyp.three
  have hu2 : u ^ 2 = 1 := helem.2 u huC.1
  have huV : u ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨v, hv⟩ ⟨u, huC.1⟩)
  have huT1 : u ∈ T1 T L := SecA.inf_centralizer_le_T1 h37 h38 hyp ⟨hCT huC, huV⟩
  have huW : u ∈ quasithinOmegaOneCenter (T1 T L) :=
    Subgroup.subset_closure ⟨⟨huT1, Subgroup.centralizer_le inf_le_left huT⟩, hu2⟩
  have hH : fsuL0 T L ⊔ T ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun s hs => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp huC.2 l hl
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp huT s hs
  have hH2 : pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
    have hu : Subgroup.zpowers u ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
        (fun g hg => by
          have hg' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
          have hgk : ∀ k : ℤ, g * u ^ k * g⁻¹ = u ^ k := fun k => by
            rw [(Commute.zpow_right hg' k).eq, mul_inv_cancel_right]
          rw [Subgroup.mem_normalizer_iff]
          intro x
          rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
          constructor
          · rintro ⟨k, rfl⟩
            exact ⟨k, (hgk k).symm⟩
          · rintro ⟨k, hk⟩
            refine ⟨k, ?_⟩
            calc u ^ k = g⁻¹ * (g * u ^ k * g⁻¹) * g := by group
              _ = g⁻¹ * u ^ k * g := by rw [hgk]
              _ = x := by rw [hk]; group)
        (IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime hu2 hu1))
    intro hb
    rw [hb, le_bot_iff, Subgroup.zpowers_eq_bot] at hu
    exact hu1 hu
  refine fun k hk => le_fsuM_of_le h331 hyp hH hH2 ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (hK hk) u huW).symm

end CFSG.Quasithin.Vol2.Ch10.SecB
