module

public import CFSG.Quasithin.Background.E6TwentyThreeKG
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.H13.KGFactE623L34
public import CFSG.Quasithin.H13.KGFactE623U34
public import CFSG.Quasithin.H13.KGFactE623Sp4

public section

namespace CFSG.Quasithin.H13.KGE623

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem e623CentA5Block_of
    (hSp : Sp44OrderThreeCent) : E6.E623CentA5Block := by
  intro Y _ _ X u hX hcases hu hu2 huC B hB hA
  obtain ⟨hS, hBle, -⟩ := hB
  have hBX : B ≤ X := le_trans hBle inf_le_left
  have hBu : B ≤ Subgroup.centralizer ({u} : Set Y) := le_trans hBle inf_le_right
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  have hπC : ∀ g : X, π g = 1 → (g : Y) ∈ Subgroup.centralizer (B : Set Y) := by
    intro g hg
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hg ⟨b, hBX hb⟩)
  have hinjC : ∀ {T : Type} [Group T] (f : X →* T), Function.Injective f →
      ∀ g : X, f g = 1 → (g : Y) ∈ Subgroup.centralizer (B : Set Y) := by
    intro T _ f hf g hg
    have h1 : g = 1 := hf (by rw [hg, map_one])
    rw [h1]
    exact one_mem _
  have hcompC : ∀ {T : Type} [Group T] (e : X ⧸ Subgroup.center X ≃* T) (g : X),
      e.toMonoidHom.comp π g = 1 → (g : Y) ∈ Subgroup.centralizer (B : Set Y) := by
    intro T _ e g hg
    refine hπC g (e.injective ?_)
    rw [map_one]
    exact hg
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rcases hcases with h | h | h | h | he | he | he | he
  ·
    have h16 := sixteen_dvd_card hBX hS hA π hπC
    rw [CFSG.Quasithin.F420.card_of_statedPSL_two_two h] at h16
    norm_num at h16
  ·
    obtain ⟨a, b, ha, ha1, hb, hb1, hab⟩ := exists_comm_of_map hBX hS hA π hπC
    exact ha1 (eq_one_of_psl34 h ha hb hb1 hab)
  ·
    have : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
    obtain ⟨a, b, ha, ha1, hb, hb1, hab⟩ := exists_comm_of_map hBX hS hA π hπC
    exact ha1 (eq_one_of_psu34 hX.2.2 h ha hb hb1 hab)
  ·
    exact false_of_sp44_block hSp hu hu2 huC h hS hA hBX hBu
  ·
    obtain ⟨e⟩ := he
    have h16 := sixteen_dvd_card hBX hS hA e.toMonoidHom (hinjC _ e.injective)
    rw [h360] at h16
    norm_num at h16
  ·
    obtain ⟨e⟩ := he
    have h16 := sixteen_dvd_card hBX hS hA e.toMonoidHom (hinjC _ e.injective)
    rw [h2520] at h16
    norm_num at h16
  ·
    obtain ⟨e⟩ := he
    have h16 := sixteen_dvd_card hBX hS hA (e.toMonoidHom.comp π) (hcompC e)
    rw [h360] at h16
    norm_num at h16
  ·
    obtain ⟨e⟩ := he
    have h16 := sixteen_dvd_card hBX hS hA (e.toMonoidHom.comp π) (hcompC e)
    rw [h2520] at h16
    norm_num at h16

end CFSG.Quasithin.H13.KGE623
