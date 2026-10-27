module

public import CFSG.Quasithin.H13.AS91Sec7Plane
public import CFSG.Quasithin.H13.AS91Sec3Ten

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

@[expose] def MeetsP (u : G ⧸ c.G1) (M : G ⧸ c.G2) (π : G ⧸ c.G3) : Prop :=
  ¬ c.LnP M π ∧ ∃ N, c.OnL u N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 u M

end Loc49

namespace M24G

section Helpers


theorem kappa_one_of_not_trioIn {U m : Finset (Finset (Fin 24))} {o : Finset (Fin 24)}
    (hU : IsSextet U) (hm : IsTrio m) (hnot : ¬ TrioIn m U) (ho : o ∈ m)
    (hoU : o ∈ octsOf U) : Kappa U m 1 := by
  obtain ⟨i, hi, -⟩ := kappa_existsUnique hU hm
  match i, hi with
  | 0, h => exact absurd h hnot
  | 1, h => exact h
  | 2, h => exact (Finset.disjoint_left.1 h.1 ho hoU).elim
  | 3, h => exact (Finset.disjoint_left.1 h.1 ho hoU).elim

end Helpers

theorem exists_octad_of_kappa_one {U m : Finset (Finset (Fin 24))} (h : Kappa U m 1) :
    ∃ o, o ∈ m ∧ o ∈ octsOf U := by
  have h' : (m ∩ octsOf U).card = 1 := h
  obtain ⟨o, ho⟩ := Finset.card_eq_one.1 h'
  have hmem : o ∈ m ∩ octsOf U := by
    rw [ho]
    exact Finset.mem_singleton_self o
  exact ⟨o, (Finset.mem_inter.1 hmem).1, (Finset.mem_inter.1 hmem).2⟩

theorem coplanar_symm_of {l k : Finset (Finset (Fin 24))} (h : Coplanar l k) :
    Coplanar k l := by
  obtain ⟨S, hS, h1, h2⟩ := h
  exact ⟨S, hS, h2, h1⟩

end M24G

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)


theorem meetsP_iff_kappa_one {g : G} {u : G ⧸ c.G1} (hg : g • c.x0 = u) {M : G ⧸ c.G2}
    {π : G ⧸ c.G3} (hM : c.OnL u M) (hπ : c.OnP u π) :
    c.MeetsP u M π ↔ M24G.Kappa (ρ.sext (g⁻¹ • π)) (ρ.trio (g⁻¹ • M)) 1 := by
  unfold Loc49.MeetsP
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hπ
  have hm : IsTrio (ρ.trio (g⁻¹ • M)) := ρ.isTrio_trio_at hg hM
  constructor
  · rintro ⟨hnot, N, hN, hNπ, hNδ⟩
    have hNU : M24G.TrioIn (ρ.trio (g⁻¹ • N)) (ρ.sext (g⁻¹ • π)) :=
      (ρ.lnP_iff_trioIn_at hg hπ hN).1 hNπ
    obtain ⟨o, hoN, hoM⟩ := Finset.not_disjoint_iff.1
      ((ρ.mem_deltaAt_one_iff_at hg hM hN).1 hNδ).2
    exact M24G.kappa_one_of_not_trioIn hU hm
      (fun hT => hnot ((ρ.lnP_iff_trioIn_at hg hπ hM).2 hT)) hoM (hNU hoN)
  · intro hκ
    obtain ⟨o, hom, hoU⟩ := M24G.exists_octad_of_kappa_one hκ
    have hnotT : ¬ M24G.TrioIn (ρ.trio (g⁻¹ • M)) (ρ.sext (g⁻¹ • π)) := by
      intro h0
      obtain ⟨i, -, huniq⟩ := M24G.kappa_existsUnique hU hm
      have e0 : (0 : Fin 4) = i := huniq 0 h0
      have e1 : (1 : Fin 4) = i := huniq 1 hκ
      exact absurd (e0.trans e1.symm) (by decide)
    have hpen : ((M24G.triosOf (ρ.sext (g⁻¹ • π))).filter (o ∈ ·)).Nonempty :=
      Finset.card_pos.1 (by rw [M24G.card_pencil hU hoU]; norm_num)
    obtain ⟨n, hn⟩ := hpen
    obtain ⟨hnT, hon⟩ := Finset.mem_filter.1 hn
    obtain ⟨-, hnT2⟩ := M24G.mem_triosOf.1 hnT
    obtain ⟨N, hN, hNπ, hNn⟩ := ρ.exists_line_of_mem_triosOf hg hπ hnT
    subst hNn
    have hne : N ≠ M := fun e => hnotT (by rw [← e]; exact hnT2)
    have hnd : ¬ Disjoint (ρ.trio (g⁻¹ • N)) (ρ.trio (g⁻¹ • M)) :=
      Finset.not_disjoint_iff.2 ⟨o, hon, hom⟩
    exact ⟨fun hL => hnotT ((ρ.lnP_iff_trioIn_at hg hπ hM).1 hL), N, hN, hNπ,
      (ρ.mem_deltaAt_one_iff_at hg hM hN).2 ⟨hne, hnd⟩⟩

theorem octad_iff {g : G} {u : G ⧸ c.G1} {L M N : G ⧸ c.G2} {π : G ⧸ c.G3}
    (hg : g • c.x0 = u) (hL : c.OnL u L) (hM : c.OnL u M) (h : M ∈ c.deltaAt 3 u L)
    (hπ : c.OnP u π) (hLπ : c.LnP L π) (hN : c.OnL u N) (hNπ : c.LnP N π)
    {y : Finset (Fin 24)} (hκ : M24G.Kappa (ρ.sext (g⁻¹ • π)) (ρ.trio (g⁻¹ • M)) 1)
    (hym : y ∈ ρ.trio (g⁻¹ • M)) (hyπ : y ∈ M24G.octsOf (ρ.sext (g⁻¹ • π))) :
    (c.CoL N M ↔ y ∈ ρ.trio (g⁻¹ • N)) ∧ (N ∈ c.deltaAt 1 u M ↔ y ∈ ρ.trio (g⁻¹ • N)) := by
  have hl : IsTrio (ρ.trio (g⁻¹ • L)) := ρ.isTrio_trio_at hg hL
  have hm : IsTrio (ρ.trio (g⁻¹ • M)) := ρ.isTrio_trio_at hg hM
  have hn : IsTrio (ρ.trio (g⁻¹ • N)) := ρ.isTrio_trio_at hg hN
  have hd : M24G.Delta (ρ.trio (g⁻¹ • L)) (ρ.trio (g⁻¹ • M)) 3 :=
    (ρ.mem_deltaAt_three_iff_at hg hL hM).1 h
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hπ
  have hlU : M24G.TrioIn (ρ.trio (g⁻¹ • L)) (ρ.sext (g⁻¹ • π)) :=
    (ρ.lnP_iff_trioIn_at hg hπ hL).1 hLπ
  have hnU : M24G.TrioIn (ρ.trio (g⁻¹ • N)) (ρ.sext (g⁻¹ • π)) :=
    (ρ.lnP_iff_trioIn_at hg hπ hN).1 hNπ
  have hcop := M24G.coplanar_iff_mem_of_trioIn hl hm hd hU hlU hκ hym hyπ hn hnU
  constructor
  · have e : c.CoL N M ↔ M24G.Coplanar (ρ.trio (g⁻¹ • N)) (ρ.trio (g⁻¹ • M)) :=
      ρ.coplanar_iff_at hg hN hM
    rw [e]
    exact ⟨fun hc => hcop.1.1 (M24G.coplanar_symm_of hc),
      fun hy => M24G.coplanar_symm_of (hcop.1.2 hy)⟩
  · rw [ρ.mem_deltaAt_iff 1 hg hM hN]
    constructor
    · intro h1
      exact hcop.1.1 ((M24G.coplanar_iff_delta hm hn).2 (Or.inr (Or.inl h1)))
    · exact hcop.2

include ρ in
theorem existsUnique_plane_meetsP (hJ : HypJ4 G z) {u : G ⧸ c.G1} {L M : G ⧸ c.G2}
    (hL : c.OnL u L) (hM : c.OnL u M) (h : M ∈ c.deltaAt 3 u L) :
    ∃! π, c.OnP u π ∧ c.LnP L π ∧ c.MeetsP u M π := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hL
  have hl : IsTrio (ρ.trio (g⁻¹ • L)) := ρ.isTrio_trio_at hg hL
  have hm : IsTrio (ρ.trio (g⁻¹ • M)) := ρ.isTrio_trio_at hg hM
  have hd : M24G.Delta (ρ.trio (g⁻¹ • L)) (ρ.trio (g⁻¹ • M)) 3 :=
    (ρ.mem_deltaAt_three_iff_at hg hL hM).1 h
  obtain ⟨U, ⟨hU, hlU, hκU⟩, huniq⟩ := M24G.existsUnique_sextet_kappa_one hl hm hd
  obtain ⟨π, hπu, hLπ, hUπ⟩ := ρ.exists_plane_of_trioIn hg hL hU hlU
  refine ⟨π, ⟨hπu, hLπ, ?_⟩, ?_⟩
  · exact (ρ.meetsP_iff_kappa_one hg hM hπu).2 (by rw [hUπ]; exact hκU)
  · rintro π' ⟨hπ'u, hLπ', hMπ'⟩
    have hU' : ρ.sext (g⁻¹ • π') = U := huniq (ρ.sext (g⁻¹ • π')) ⟨ρ.isSextet_sext_at hg hπ'u,
      (ρ.lnP_iff_trioIn_at hg hπ'u hL).1 hLπ', (ρ.meetsP_iff_kappa_one hg hM hπ'u).1 hMπ'⟩
    have hσ' : CInc c.G1 c.G3 c.x0 (g⁻¹ • π') := by
      rw [← hg] at hπ'u
      exact (cInc_smul_inv_iff g c.x0 π').1 hπ'u
    have hσ : CInc c.G1 c.G3 c.x0 (g⁻¹ • π) := by
      rw [← hg] at hπu
      exact (cInc_smul_inv_iff g c.x0 π).1 hπu
    exact MulAction.injective g⁻¹ (ρ.sext_injOn hσ' hσ (hU'.trans hUπ.symm))

include ρ in
theorem coL_iff_delta_one_of_meetsP {u : G ⧸ c.G1} {L M N : G ⧸ c.G2} {π : G ⧸ c.G3}
    (hL : c.OnL u L) (hM : c.OnL u M) (h : M ∈ c.deltaAt 3 u L) (hπ : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) (hN : c.OnL u N) (hNπ : c.LnP N π) :
    c.CoL N M ↔ N ∈ c.deltaAt 1 u M := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hL
  have hκ := (ρ.meetsP_iff_kappa_one hg hM hπ).1 hMπ
  obtain ⟨y, hym, hyπ⟩ := M24G.exists_octad_of_kappa_one hκ
  exact (ρ.octad_iff hg hL hM h hπ hLπ hN hNπ hκ hym hyπ).1.trans
    (ρ.octad_iff hg hL hM h hπ hLπ hN hNπ hκ hym hyπ).2.symm

include ρ in
theorem ncard_delta_one_of_meetsP {u : G ⧸ c.G1} {L M : G ⧸ c.G2} {π : G ⧸ c.G3}
    (hL : c.OnL u L) (hM : c.OnL u M) (h : M ∈ c.deltaAt 3 u L) (hπ : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) :
    {N | c.OnL u N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 u M}.ncard = 3 := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hL
  have hκ := (ρ.meetsP_iff_kappa_one hg hM hπ).1 hMπ
  obtain ⟨y, hym, hyπ⟩ := M24G.exists_octad_of_kappa_one hκ
  have hcount := M24G.ncard_trioIn_mem (ρ.isTrio_trio_at hg hL) (ρ.isTrio_trio_at hg hM)
    ((ρ.mem_deltaAt_three_iff_at hg hL hM).1 h) (ρ.isSextet_sext_at hg hπ)
    ((ρ.lnP_iff_trioIn_at hg hπ hL).1 hLπ) hκ hym hyπ
  rw [← hcount]
  refine Set.ncard_congr (fun N _ => ρ.trio (g⁻¹ • N)) (fun N hN => ?_)
    (fun N N' hN hN' e => ?_) (fun k hk => ?_)
  · obtain ⟨hN1, hN2, hN3⟩ := hN
    rw [Set.mem_setOf_eq]
    exact ⟨ρ.isTrio_trio_at hg hN1, (ρ.lnP_iff_trioIn_at hg hπ hN1).1 hN2,
      ((ρ.octad_iff hg hL hM h hπ hLπ hN1 hN2 hκ hym hyπ).2.1 hN3)⟩
  · obtain ⟨hN1, -, -⟩ := hN
    obtain ⟨hN1', -, -⟩ := hN'
    exact ρ.eq_of_trio_at hg hN1 hN1' e
  · obtain ⟨hk1, hk2, hk3⟩ := hk
    obtain ⟨N, hN1, hN2, hNk⟩ :=
      ρ.exists_line_of_mem_triosOf hg hπ ((M24G.mem_triosOf (U := ρ.sext (g⁻¹ • π))).2 ⟨hk1, hk2⟩)
    refine ⟨N, ?_, hNk⟩
    rw [Set.mem_setOf_eq]
    exact ⟨hN1, hN2,
      (ρ.octad_iff hg hL hM h hπ hLπ hN1 hN2 hκ hym hyπ).2.2 (by rw [hNk]; exact hk3)⟩

include ρ in
theorem exists_delta_one_of_meetsP {u : G ⧸ c.G1} {L M : G ⧸ c.G2} {π : G ⧸ c.G3}
    (hL : c.OnL u L) (hM : c.OnL u M) (h : M ∈ c.deltaAt 3 u L) (hπ : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) :
    ∃ N₀, c.OnL u N₀ ∧ c.LnP N₀ π ∧ N₀ ∈ c.deltaAt 1 u M ∧ N₀ ∈ c.deltaAt 1 u L ∧
      ∀ N, c.OnL u N → c.LnP N π → N ∈ c.deltaAt 1 u M → N ≠ N₀ → N ∈ c.deltaAt 2 u L := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hL
  have hκ := (ρ.meetsP_iff_kappa_one hg hM hπ).1 hMπ
  obtain ⟨y, hym, hyπ⟩ := M24G.exists_octad_of_kappa_one hκ
  obtain ⟨k₀, hk₀, hk₀U, hyk₀, hLk₀, hrest⟩ := M24G.exists_delta_one_trioIn
    (ρ.isTrio_trio_at hg hL) (ρ.isTrio_trio_at hg hM)
    ((ρ.mem_deltaAt_three_iff_at hg hL hM).1 h) (ρ.isSextet_sext_at hg hπ)
    ((ρ.lnP_iff_trioIn_at hg hπ hL).1 hLπ) hκ hym hyπ
  obtain ⟨N₀, hN₀, hN₀π, hN₀k⟩ :=
    ρ.exists_line_of_mem_triosOf hg hπ ((M24G.mem_triosOf (U := ρ.sext (g⁻¹ • π))).2 ⟨hk₀, hk₀U⟩)
  subst hN₀k
  refine ⟨N₀, hN₀, hN₀π, (ρ.octad_iff hg hL hM h hπ hLπ hN₀ hN₀π hκ hym hyπ).2.2 hyk₀, ?_, ?_⟩
  · rw [ρ.mem_deltaAt_iff 1 hg hL hN₀]
    exact hLk₀
  · intro N hN hNπ hNδ hne
    have hyN : y ∈ ρ.trio (g⁻¹ • N) := (ρ.octad_iff hg hL hM h hπ hLπ hN hNπ hκ hym hyπ).2.1 hNδ
    have hkne : ρ.trio (g⁻¹ • N) ≠ ρ.trio (g⁻¹ • N₀) := fun e => hne (ρ.eq_of_trio_at hg hN hN₀ e)
    rw [ρ.mem_deltaAt_iff 2 hg hL hN]
    exact hrest _ (ρ.isTrio_trio_at hg hN) ((ρ.lnP_iff_trioIn_at hg hπ hN).1 hNπ) hyN hkne

include ρ in
theorem delta_one_of_meetsP {u : G ⧸ c.G1} {L M N N' : G ⧸ c.G2} {π : G ⧸ c.G3}
    (hL : c.OnL u L) (hM : c.OnL u M) (h : M ∈ c.deltaAt 3 u L) (hπ : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) (hN : c.OnL u N) (hNπ : c.LnP N π)
    (hNM : N ∈ c.deltaAt 1 u M) (hN' : c.OnL u N') (hN'π : c.LnP N' π)
    (hN'M : N' ∈ c.deltaAt 1 u M) (hNN' : N ≠ N') : N' ∈ c.deltaAt 1 u N := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hL
  have hκ := (ρ.meetsP_iff_kappa_one hg hM hπ).1 hMπ
  obtain ⟨y, hym, hyπ⟩ := M24G.exists_octad_of_kappa_one hκ
  have hyN : y ∈ ρ.trio (g⁻¹ • N) := (ρ.octad_iff hg hL hM h hπ hLπ hN hNπ hκ hym hyπ).2.1 hNM
  have hyN' : y ∈ ρ.trio (g⁻¹ • N') :=
    (ρ.octad_iff hg hL hM h hπ hLπ hN' hN'π hκ hym hyπ).2.1 hN'M
  rw [ρ.mem_deltaAt_one_iff_at hg hN hN']
  exact ⟨Ne.symm hNN', fun hd => Finset.disjoint_left.1 hd hyN' hyN⟩

end ResM24

end CFSG.Quasithin.H13.AS91
