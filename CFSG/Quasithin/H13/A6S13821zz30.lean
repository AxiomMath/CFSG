module

public import CFSG.Quasithin.H13.A6S13821zz18
public import CFSG.Quasithin.H13.A6S13821zz26
public import CFSG.Quasithin.H13.A6S13821zz29

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_su38_13820b
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    (h45 : AsB45) {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (hL1K : S.L1 ≤ K)
    (hU : IsPSU 3 2 3 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) : False := by
  classical
  obtain ⟨hF, I, -, hIU, -, hnat, hkerK⟩ :=
    S.exists_natural_su38_13820b h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 h42 h45 hC
      hL1K hU hZ
  obtain ⟨hS, hH, hK, hKn, hHK, -, -⟩ := hC
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHKT : H = K ⊔ T := by
    rw [hHK, ← sup_assoc, sup_eq_left.mpr hL1K]
  have hFe := factElem hF hIU
  have hV₁ := hF.H_le_normalizer_V₁
  have hIH := le_normalizer_conjClosure I H
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  set ψ := actH hV₁ hIH with hψ
  have hHU := le_normalizer_conjClosure S.V3 H
  have hXU : conjClosure I H ≤ conjClosure S.V3 H := conjClosure_le fun h hh x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHU hh) x).mp (hIU hx)
  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by
      simpa using (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H))).2 w w.2)
  refine S.false_of_section_13820b hS hH hKn hHKT ψ hXU hIH (tildeHom hIHN)
    (tildeHom_surjective hIHN) (fun x hx => Subtype.ext (by
      rw [tildeHom_coe]
      exact secMk_eq_one_iff.mpr hx)) (fun h x hx => ?_) (fun h hhK h1 => ?_) ?_
  ·
    have e1 : tildeHom hIHN x = modMk hIHN x x.2 := rfl
    rw [e1, actH_modMk hV₁ hIHN hIH h x.2]
    rfl
  ·
    rw [hψ, A6Tv.actH_eq_one_iff hV₁ hIHN hIH] at h1
    exact hkerK h hhK h1
  ·
    intro A hA hAel D hD a₁ hDA
    by_contra hA1
    refine A6S20.false_of_su3_quad hW2 le_rfl hnat ?_ hAel hA1 hD a₁ hDA
    intro a ha l hl
    obtain ⟨h, rfl⟩ := hA ha
    rw [autIH_eq_map hF hKH] at hl ⊢
    obtain ⟨k, hk, rfl⟩ := hl
    refine ⟨h * k * h⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKn h.2) _).mp (Subgroup.mem_subgroupOf.mp hk)

end Setting4

end CFSG.Quasithin.H13.A6
