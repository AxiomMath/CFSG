module

public import CFSG.Quasithin.Vol2.Ch11SecSRole
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem fsuV_inf_centralizer_L_eq_bot (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : StarHyp G T L I V₁ V₂ X K) : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  set P := fsuV T I ⊓ Subgroup.centralizer (L : Set G) with hPdef
  have hP2 : IsPGroup 2 ↥P := (SecA.isPGroup_fsuV h.hyp).to_le inf_le_left
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hne, hP2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hCN : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hLN : L ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.le_centralizer_iff.mp inf_le_right).trans hCN
  have hNC : Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hTN : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨T_le_normalizer_fsuV T I ht, hNC (h.hyp.normal ht)⟩
  have hKN : K ≤ Subgroup.normalizer (P : Set G) :=
    (h.le_cent.trans (Subgroup.centralizer_le h.v₁.1.1)).trans hCN
  have hU := lemma_1_2_7_three h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian h37 h38 h39
    h.sylow h.hyp.fsu.maximal
  have hcc : conjClosure L T = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (h.hyp.normal ht) l).1 hl)
      (le_conjClosure L T)
  rw [hcc] at hU
  have hM := hU.2 M' ⟨hM', (sup_le hLN hTN).trans hle⟩
  rw [hM] at hle
  exact h.not_le (hKN.trans hle)

theorem card_V₁ (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : StarHyp G T L I V₁ V₂ X K) : Nat.card ↥V₁ = 4 :=
  card_vi_one h.v₁ (fsuV_inf_centralizer_L_eq_bot h37 h38 h39 h)

theorem vertex_le (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) :
    k0Of K P₂ ⊔ bigB (k0Of K P₂) (LOf L V₂) (sXT X T) ≤ k0Of K P₂ ⊔ (X ⊔ T) :=
  sup_le le_sup_left (sup_le (sup_le (inf_le_left.trans le_sup_left)
    ((borelOf_L₂_le hN h1102 h cL).trans le_sup_right))
    ((sXT_le_T h.sylow).trans (le_sup_right.trans le_sup_right)))

theorem vertex_le_normalizer_k0Of (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) :
    k0Of K P₂ ⊔ bigB (k0Of K P₂) (LOf L V₂) (sXT X T) ≤
      Subgroup.normalizer (k0Of K P₂ : Set G) :=
  (vertex_le hN h1102 h cL).trans (sup_le Subgroup.le_normalizer
    (sup_le (h.cartan_le_normalizer_k0Of hN h1102 hP) (h.T_le_normalizer_k0Of hP)))

theorem vertex_le_normalizer_V₁ (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X) :
    k0Of K P₂ ⊔ bigB (k0Of K P₂) (LOf L V₂) (sXT X T) ≤ Subgroup.normalizer (V₁ : Set G) :=
  (vertex_le hN h1102 h cL).trans (sup_le ((k0Of_le K P₂).trans h.K_le_normalizer_V₁)
    (sup_le (cartan_le_normalizer_Vi hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan)
      h.T_le_normalizer_V₁))

theorem V₁_le_vertex (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) :
    V₁ ≤ k0Of K P₂ ⊔ bigB (k0Of K P₂) (LOf L V₂) (sXT X T) :=
  (V₁_le_sXT hN h1102 h).trans (le_sup_right.trans le_sup_right)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
