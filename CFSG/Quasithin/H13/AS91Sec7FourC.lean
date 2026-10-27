module

public import CFSG.Quasithin.H13.AS91Sec7Three
public import CFSG.Quasithin.H13.AS91Sec7FourA
public import CFSG.Quasithin.H13.AS91Sec7FourB

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem adj_smul_iff₄ (g : G) (u v : G ⧸ c.G1) :
    c.Delta.Adj (g • u) (g • v) ↔ c.Delta.Adj u v :=
  CFSG.Quasithin.GraphAction.adj_smul g u v

@[expose] def InDeltaP (x y : G ⧸ c.G1) (π : G ⧸ c.G3) (w : G ⧸ c.G1) : Prop :=
  c.Delta.Adj x w ∧ c.Delta.Adj y w ∧ c.OnP w π

theorem stmt5_3_3_at (h533 : Stmt5_3_3) (hJ : HypJ4 G z) {a : G ⧸ c.G1} {m : G ⧸ c.G2}
    {σ : G ⧸ c.G3} (ha : c.OnP a σ) (hm : c.LnP m σ) (ham : ¬ c.OnL a m) :
    (∀ b, c.OnL b m → c.Delta.Adj a b) ∨ {b | c.OnL b m ∧ c.Delta.Adj a b}.ncard = 3 := by
  obtain ⟨g, hga, hgσ⟩ := c.exists_frameP ha
  have hga' : g⁻¹ • a = c.x0 := by rw [← hga, inv_smul_smul]
  have hgσ' : g⁻¹ • σ = c.pi0 := by rw [← hgσ, inv_smul_smul]
  have haP : g⁻¹ • a ∈ c.ptsP := by
    rw [hga']
    exact c.x0_mem_ptsP
  have hmP : g⁻¹ • m ∈ c.lnsP := by
    have h := (cInc_smul c.G2 c.G3 g⁻¹ m σ).2 hm
    rwa [hgσ'] at h
  have hnot : ¬ CInc c.G1 c.G2 (g⁻¹ • a) (g⁻¹ • m) := by
    rw [cInc_smul]
    exact ham
  rcases h533 G z hJ c (g⁻¹ • a) haP (g⁻¹ • m) hmP hnot with h | h
  · refine Or.inl fun b hb => ?_
    have hb' : CInc c.G1 c.G2 (g⁻¹ • b) (g⁻¹ • m) := (cInc_smul c.G1 c.G2 g⁻¹ b m).2 hb
    exact (c.adj_smul_iff₄ g⁻¹ a b).1 (h (g⁻¹ • b) hb')
  · refine Or.inr ?_
    have hset : {b | c.OnL b m ∧ c.Delta.Adj a b} =
        (g • ·) '' {b | CInc c.G1 c.G2 b (g⁻¹ • m) ∧ c.Delta.Adj (g⁻¹ • a) b} := by
      ext b
      constructor
      · rintro ⟨hb, hab⟩
        exact ⟨g⁻¹ • b, ⟨(cInc_smul c.G1 c.G2 g⁻¹ b m).2 hb, (c.adj_smul_iff₄ g⁻¹ a b).2 hab⟩,
          smul_inv_smul g b⟩
      · rintro ⟨b', ⟨hb', hab'⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · have h := (cInc_smul c.G1 c.G2 g b' (g⁻¹ • m)).2 hb'
          rwa [smul_inv_smul] at h
        · have h := (c.adj_smul_iff₄ g (g⁻¹ • a) b').2 hab'
          rwa [smul_inv_smul] at h
    rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g)]
    exact h

theorem coL_of_triangle (hI : Sec7Inputs) (hJ : HypJ4 G z) {u d y : G ⧸ c.G1}
    {M N : G ⧸ c.G2} (hud : c.Delta.Adj u d) (hdy : c.Delta.Adj d y) (huy : c.Delta.Adj u y)
    (hMu : c.OnL u M) (hMy : c.OnL y M) (hNu : c.OnL u N) (hNd : c.OnL d N) : c.CoL N M := by
  obtain ⟨σ, hσu, hσd, hσy⟩ := hI.s55 G z hJ c u d y hud hdy huy
  exact ⟨σ, c.lnP_of_adj hI.gamma2 hJ hσu hσd hud hNu hNd,
    c.lnP_of_adj hI.gamma2 hJ hσu hσy huy hMu hMy⟩

structure DiscData (x y : G ⧸ c.G1) (π : G ⧸ c.G3) : Prop where
  x_on : c.OnP x π
  triple : ∀ d, c.InDeltaP x y π d → c.Rh 2 x d y ∧ ¬ c.Rh 1 x d y
  meets : ∀ d M, c.InDeltaP x y π d → c.OnL d M → c.OnL y M → c.MeetsP d M π

structure AtPt (x y : G ⧸ c.G1) (π : G ⧸ c.G3) (d : G ⧸ c.G1) (L M : G ⧸ c.G2) : Prop where
  inD : c.InDeltaP x y π d
  L_d : c.OnL d L
  L_x : c.OnL x L
  M_d : c.OnL d M
  M_y : c.OnL y M

structure PenLine (π : G ⧸ c.G3) (d : G ⧸ c.G1) (L M m : G ⧸ c.G2) : Prop where
  on_d : c.OnL d m
  lnP : c.LnP m π
  delta1 : m ∈ c.deltaAt 1 d M
  delta2 : m ∈ c.deltaAt 2 d L

section Data

variable {c} {x y : G ⧸ c.G1} {π : G ⧸ c.G3} {d : G ⧸ c.G1} {L M m : G ⧸ c.G2}

theorem AtPt.delta3 (hI : Sec7Inputs) (hJ : HypJ4 G z) (S : c.DiscData x y π)
    (A : c.AtPt x y π d L M) : M ∈ c.deltaAt 3 d L :=
  c.rh21_mem_delta3 hI hJ (S.triple d A.inD).1 (S.triple d A.inD).2 A.L_d A.L_x A.M_d A.M_y

theorem AtPt.lnP (hI : Sec7Inputs) (hJ : HypJ4 G z) (S : c.DiscData x y π)
    (A : c.AtPt x y π d L M) : c.LnP L π :=
  c.lnP_of_adj hI.gamma2 hJ A.inD.2.2 S.x_on A.inD.1.symm A.L_d A.L_x

theorem AtPt.meetsP (S : c.DiscData x y π) (A : c.AtPt x y π d L M) : c.MeetsP d M π :=
  S.meets d M A.inD A.M_d A.M_y

theorem PenLine.adj_x (hI : Sec7Inputs) (hJ : HypJ4 G z) (A : c.AtPt x y π d L M)
    (P : c.PenLine π d L M m) {a : G ⧸ c.G1} (ha : c.OnL a m) : c.Delta.Adj x a :=
  c.stmt7_1_two hI.s54 hJ A.L_d A.L_x A.inD.1.ne P.delta2 ha

theorem PenLine.ncard_y (hI : Sec7Inputs) (hJ : HypJ4 G z) (A : c.AtPt x y π d L M)
    (P : c.PenLine π d L M m) : {a | c.OnL a m ∧ c.Delta.Adj y a}.ncard = 3 :=
  c.stmt7_1_one hI.s54 hJ A.M_d A.M_y A.inD.2.1.ne P.delta1

theorem PenLine.not_onL_x (hI : Sec7Inputs) (hJ : HypJ4 G z) (A : c.AtPt x y π d L M)
    (P : c.PenLine π d L M m) : ¬ c.OnL x m := fun h => (P.adj_x hI hJ A h).ne rfl

theorem PenLine.inD (hI : Sec7Inputs) (hJ : HypJ4 G z) (A : c.AtPt x y π d L M)
    (P : c.PenLine π d L M m) {a : G ⧸ c.G1} (ha : c.OnL a m) (hya : c.Delta.Adj y a) :
    c.InDeltaP x y π a :=
  ⟨P.adj_x hI hJ A ha, hya, c.inc_pt_plane ha P.lnP⟩

end Data

end Loc49

namespace M24G


theorem card_inter_eq_three {U : Finset (Finset (Fin 24))} (hU : IsSextet U)
    {S : Finset (Finset (Finset (Fin 24)))} (hSP : S ⊆ triosOf U)
    (h : ∀ k ∈ S, ∃ O₁ ∈ spreadsOf U, ∃ O₂ ∈ spreadsOf U, O₁ ≠ O₂ ∧ k ∈ O₁ ∧ k ∈ O₂ ∧
      (O₁ ∩ S).card = 3 ∧ (O₂ ∩ S).card = 3) :
    ∀ D ∈ spreadsOf U, ¬ Disjoint D S → (D ∩ S).card = 3 := by
  intro D hD hDS
  obtain ⟨k, hkD, hkS⟩ := Finset.not_disjoint_iff.1 hDS
  obtain ⟨O₁, hO₁, O₂, hO₂, hne, hk₁, hk₂, h₁, h₂⟩ := h k hkS
  have hcard := (stmt2_1_1_triosOf hU).1 k (hSP hkS)
  have hsub : ({D, O₁, O₂} : Finset (Finset (Finset (Finset (Fin 24))))) ⊆
      (spreadsOf U).filter (k ∈ ·) := by
    intro O hO
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO
    rw [Finset.mem_filter]
    rcases hO with rfl | rfl | rfl
    exacts [⟨hD, hkD⟩, ⟨hO₁, hk₁⟩, ⟨hO₂, hk₂⟩]
  by_cases h₁D : D = O₁
  · rw [h₁D]
    exact h₁
  by_cases h₂D : D = O₂
  · rw [h₂D]
    exact h₂
  exfalso
  have h3 : ({D, O₁, O₂} : Finset (Finset (Finset (Finset (Fin 24))))).card = 3 :=
    Finset.card_eq_three.2 ⟨D, O₁, O₂, h₁D, h₂D, hne, rfl⟩
  have hle := Finset.card_le_card hsub
  omega

end M24G

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

open Classical in
@[expose] noncomputable def discTrios (x y : G ⧸ c.G1) (π : G ⧸ c.G3) (g : G) :
    Finset (Finset (Finset (Fin 24))) :=
  (M24G.triosOf (ρ.sext (g⁻¹ • π))).filter fun t =>
    ∃ n, c.OnL x n ∧ c.LnP n π ∧ ρ.trio (g⁻¹ • n) = t ∧ ∃ w, c.InDeltaP x y π w ∧ c.OnL w n

theorem mem_discTrios {x y : G ⧸ c.G1} {π : G ⧸ c.G3} {g : G}
    {t : Finset (Finset (Fin 24))} :
    t ∈ ρ.discTrios x y π g ↔ t ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)) ∧
      ∃ n, c.OnL x n ∧ c.LnP n π ∧ ρ.trio (g⁻¹ • n) = t ∧
        ∃ w, c.InDeltaP x y π w ∧ c.OnL w n := by
  classical
  unfold discTrios
  rw [Finset.mem_filter]

section Two


theorem trio_mem_discTrios_iff {x y : G ⧸ c.G1} {π : G ⧸ c.G3} {g : G} (hg : g • c.x0 = x)
    (hxπ : c.OnP x π) {n : G ⧸ c.G2} (hxn : c.OnL x n) (hnπ : c.LnP n π) :
    ρ.trio (g⁻¹ • n) ∈ ρ.discTrios x y π g ↔ ∃ w, c.InDeltaP x y π w ∧ c.OnL w n := by
  rw [mem_discTrios]
  constructor
  · rintro ⟨-, n', hxn', -, he, w, hw, hwn'⟩
    have hn : n' = n := ρ.eq_of_trio_at hg hxn' hxn he
    rw [hn] at hwn'
    exact ⟨w, hw, hwn'⟩
  · rintro ⟨w, hw, hwn⟩
    exact ⟨ρ.trio_mem_triosOf hg hxπ hxn hnπ, n, hxn, hnπ, rfl, w, hw, hwn⟩

end Two

section Five


include ρ in
theorem line_mem_delta_one (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) {d : G ⧸ c.G1} (hd : c.InDeltaP x y π d)
    (hdu : d ≠ u) {N : G ⧸ c.G2} (hNu : c.OnL u N) (hNd : c.OnL d N) :
    c.LnP N π ∧ N ∈ c.deltaAt 1 u M := by
  obtain ⟨hxu, huy, -⟩ := c.rh21_path h2 h1
  have hud : c.Delta.Adj u d := c.rh21_clique hI hJ h2 h1 ⟨hxu, huy.symm, hπu⟩ hd hdu.symm
  have hNπ : c.LnP N π := c.lnP_of_adj hI.gamma2 hJ hπu hd.2.2 hud hNu hNd
  have hcop : c.CoL N M := c.coL_of_triangle hI hJ hud hd.2.1.symm huy hMu hMy hNu hNd
  have hδ3 : M ∈ c.deltaAt 3 u L := c.rh21_mem_delta3 hI hJ h2 h1 hLu hLx hMu hMy
  exact ⟨hNπ, (ρ.coL_iff_delta_one_of_meetsP hLu hMu hδ3 hπu hLπ hMπ hNu hNπ).1 hcop⟩

include ρ in
theorem line_mem_delta_one_or_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) {d : G ⧸ c.G1} (hd : c.InDeltaP x y π d)
    (hdu : d ≠ u) {N : G ⧸ c.G2} (hNu : c.OnL u N) (hNd : c.OnL d N) :
    N ∈ c.deltaAt 1 u L ∨ N ∈ c.deltaAt 2 u L := by
  obtain ⟨hNπ, -⟩ := ρ.line_mem_delta_one hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd hdu hNu hNd
  obtain ⟨-, huy, -⟩ := c.rh21_path h2 h1
  rcases (ρ.coL_iff_deltaAt hLu hNu).1 ⟨π, hLπ, hNπ⟩ with h0 | h | h
  · exfalso
    have hNL : N = L := (ρ.mem_deltaAt_zero_iff hLu hNu).1 h0
    have hdL : c.OnL d L := by
      rw [← hNL]
      exact hNd
    exact hdu (c.eq_of_not_coL hI.s55 hI.gamma2 hJ hLu hMu (c.rh21_not_coL h2 h1 hLu hLx hMu hMy)
      hMy huy.ne.symm hdL hd.2.1)
  · exact Or.inl h
  · exact Or.inr h

include ρ in
theorem inD_meetsP (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) {d : G ⧸ c.G1} (hd : c.InDeltaP x y π d)
    {M' : G ⧸ c.G2} (hdM' : c.OnL d M') (hyM' : c.OnL y M') : c.MeetsP d M' π := by
  have hxπ : c.OnP x π := c.inc_pt_plane hLx hLπ
  have hyπ : ¬ c.OnP y π := c.rh21_not_onP hI hJ h2 h1 hxπ
  obtain ⟨hxu, huy, -⟩ := c.rh21_path h2 h1
  by_cases hdu : d = u
  · rw [hdu] at hdM' ⊢
    have hMM' : M' = M := c.eq_of_onL hI.lineU hJ huy.ne hdM' hyM' hMu hMy
    rw [hMM']
    exact hMπ
  · have hud : c.Delta.Adj u d :=
      c.rh21_clique hI hJ h2 h1 ⟨hxu, huy.symm, hπu⟩ hd (Ne.symm hdu)
    obtain ⟨N, hNu, hNd⟩ := c.exists_onL_of_adj hud
    obtain ⟨hNπ, hNM⟩ :=
      ρ.line_mem_delta_one hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd hdu hNu hNd
    refine ⟨fun h => hyπ (c.inc_pt_plane hyM' h), N, hNd, hNπ, ?_⟩
    have hMN : M ∈ c.deltaAt 1 u N := ρ.deltaAt_symm 1 hMu hNu hNM
    have hM'N : M' ∈ c.deltaAt 1 d N :=
      (hI.s56 G z hJ c u d y hud hd.2.1.symm huy).2.2 N M M' 1 hNu hNd hMu hMy hdM' hyM' hMN
    exact ρ.deltaAt_symm 1 hNd hdM' hM'N

include ρ in
theorem exists_two_lines (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1}
    {π : G ⧸ c.G3} {d : G ⧸ c.G1} {L M : G ⧸ c.G2} (S : c.DiscData x y π)
    (A : c.AtPt x y π d L M) :
    ∃ m₁ m₂, m₁ ≠ m₂ ∧ c.PenLine π d L M m₁ ∧ c.PenLine π d L M m₂ := by
  have hδ3 := A.delta3 hI hJ S
  have hLπ := A.lnP hI hJ S
  have hMπ := A.meetsP S
  have hcard := ρ.ncard_delta_one_of_meetsP A.L_d A.M_d hδ3 A.inD.2.2 hLπ hMπ
  obtain ⟨N₀, hN₀, hN₀π, hN₀M, -, hrest⟩ :=
    ρ.exists_delta_one_of_meetsP A.L_d A.M_d hδ3 A.inD.2.2 hLπ hMπ
  have hmem : N₀ ∈ {N | c.OnL d N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 d M} := ⟨hN₀, hN₀π, hN₀M⟩
  have h2 : ({N | c.OnL d N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 d M} \ {N₀}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem hmem, hcard]
  obtain ⟨m₁, m₂, hne, hT⟩ := Set.ncard_eq_two.1 h2
  have h₁ : m₁ ∈ {N | c.OnL d N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 d M} \ {N₀} := by
    rw [hT]
    simp
  have h₂ : m₂ ∈ {N | c.OnL d N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 d M} \ {N₀} := by
    rw [hT]
    simp
  refine ⟨m₁, m₂, hne, ⟨h₁.1.1, h₁.1.2.1, h₁.1.2.2, ?_⟩, ⟨h₂.1.1, h₂.1.2.1, h₂.1.2.2, ?_⟩⟩
  · exact hrest m₁ h₁.1.1 h₁.1.2.1 h₁.1.2.2 fun e => h₁.2 (by rw [e]; rfl)
  · exact hrest m₂ h₂.1.1 h₂.1.2.1 h₂.1.2.2 fun e => h₂.2 (by rw [e]; rfl)

include ρ in
theorem adj_of_inD_on_line (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1}
    {π : G ⧸ c.G3} {d : G ⧸ c.G1} {L M m : G ⧸ c.G2} (S : c.DiscData x y π)
    (A : c.AtPt x y π d L M) (P : c.PenLine π d L M m) {w : G ⧸ c.G1} (hwm : c.OnL w m)
    {n : G ⧸ c.G2} (hxn : c.OnL x n) (hwn : c.OnL w n) {d' : G ⧸ c.G1}
    (hd' : c.InDeltaP x y π d') (hd'n : c.OnL d' n) : c.Delta.Adj y w := by
  by_contra hwy
  have hd := A.inD
  have hwd : w ≠ d := fun h => hwy (by rw [h]; exact hd.2.1)
  have hdn : ¬ c.OnL d n := by
    intro hdn
    have hnL : n = L := c.eq_of_onL hI.lineU hJ hd.1.ne hxn hdn A.L_x A.L_d
    have hwL : c.OnL w L := by
      rw [← hnL]
      exact hwn
    have hmL : m = L := c.eq_of_onL hI.lineU hJ hwd hwm P.on_d hwL A.L_d
    obtain ⟨i, -, hu⟩ := ρ.deltaAt_existsUnique A.L_d P.on_d
    have h0 : m ∈ c.deltaAt 0 d L := (ρ.mem_deltaAt_zero_iff A.L_d P.on_d).2 hmL
    exact absurd ((hu 0 h0).trans (hu 2 P.delta2).symm) (by decide)
  have hd'w : d' ≠ w := fun h => hwy (by rw [← h]; exact hd'.2.1)
  have hd'd : d' ≠ d := fun h => hdn (by rw [← h]; exact hd'n)
  have hdw : c.Delta.Adj d w := c.adj_of_onL hwd.symm P.on_d hwm
  have hdd' : c.Delta.Adj d d' :=
    c.rh21_clique hI hJ (S.triple d hd).1 (S.triple d hd).2 hd hd' hd'd.symm
  have hnπ : c.LnP n π := c.lnP_of_adj hI.gamma2 hJ S.x_on hd'.2.2 hd'.1 hxn hd'n
  obtain ⟨gd, hgd, -⟩ := c.exists_frame A.L_d
  have hLπ := A.lnP hI hJ S
  have hδ3 := A.delta3 hI hJ S
  have hMπ := A.meetsP S
  rcases c.stmt5_3_3_at hI.s533 hJ hd.2.2 hnπ hdn with h5 | h3
  ·
    obtain ⟨Od, hOd, hOdp⟩ := ρ.stmt7_3_two hI hJ hgd hd.2.2 hnπ hdn h5
    obtain ⟨m', hdm', hd'm'⟩ := c.exists_onL_of_adj hdd'
    obtain ⟨hm'π, hm'M⟩ := ρ.line_mem_delta_one hI hJ (S.triple d hd).1 (S.triple d hd).2
      A.L_d A.L_x A.M_d A.M_y hd.2.2 hLπ hMπ hd' hd'd hdm' hd'm'
    have hmm' : m ≠ m' := by
      intro h
      have hd'm : c.OnL d' m := by
        rw [h]
        exact hd'm'
      have hmn : m = n := c.eq_of_onL hI.lineU hJ hd'w.symm hwm hd'm hwn hd'n
      exact hdn (by rw [← hmn]; exact P.on_d)
    have h1' : m' ∈ c.deltaAt 1 d m :=
      ρ.delta_one_of_meetsP A.L_d A.M_d hδ3 hd.2.2 hLπ hMπ P.on_d P.lnP P.delta1 hdm' hm'π hm'M
        hmm'
    obtain ⟨-, hnd⟩ := (ρ.mem_deltaAt_one_iff_at hgd P.on_d hdm').1 h1'
    have hk : ρ.trio (gd⁻¹ • m) ∈ Od := (hOdp m P.on_d).1 ⟨w, hwn, hwm⟩
    have hk' : ρ.trio (gd⁻¹ • m') ∈ Od := (hOdp m' hdm').1 ⟨d', hd'n, hd'm'⟩
    have hne : ρ.trio (gd⁻¹ • m) ≠ ρ.trio (gd⁻¹ • m') := fun e =>
      hmm' (ρ.eq_of_trio_at hgd P.on_d hdm' e)
    exact hnd (((M24G.mem_spreadsOf.1 hOd).2 _ hk).2.2 _ hk' hne).symm
  ·
    obtain ⟨o, -, hop⟩ := ρ.stmt7_3_one hI hJ hgd hd.2.2 hnπ hdn h3
    have hoL : o ∈ ρ.trio (gd⁻¹ • L) := ((hop L A.L_d).1 ⟨x, hxn, hd.1.symm, A.L_x⟩).2
    have hom : o ∈ ρ.trio (gd⁻¹ • m) := ((hop m P.on_d).1 ⟨w, hwn, hdw, hwm⟩).2
    obtain ⟨hdis, -⟩ := (ρ.mem_deltaAt_two_iff_at hgd A.L_d P.on_d).1 P.delta2
    exact Finset.disjoint_left.1 hdis hom hoL

include ρ in
theorem spread_ne (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1} {π : G ⧸ c.G3}
    {d : G ⧸ c.G1} {L M m₁ m₂ : G ⧸ c.G2} (S : c.DiscData x y π) (A : c.AtPt x y π d L M)
    (P₁ : c.PenLine π d L M m₁) (P₂ : c.PenLine π d L M m₂) (hne : m₁ ≠ m₂) {g : G}
    {O₁ O₂ : Finset (Finset (Finset (Fin 24)))}
    (hO₁ : ∀ n, c.OnL x n →
      ((∃ w, c.OnL w m₁ ∧ c.OnL w n) ↔ ρ.trio (g⁻¹ • n) ∈ O₁))
    (hO₂ : ∀ n, c.OnL x n →
      ((∃ w, c.OnL w m₂ ∧ c.OnL w n) ↔ ρ.trio (g⁻¹ • n) ∈ O₂)) : O₁ ≠ O₂ := by
  intro hO
  rw [← hO] at hO₂
  have hA := P₁.ncard_y hI hJ A
  obtain ⟨w, ⟨hwm₁, hyw⟩, hwd⟩ := Set.exists_ne_of_one_lt_ncard
    (s := {a | c.OnL a m₁ ∧ c.Delta.Adj y a}) (by omega) d
  have hwD : c.InDeltaP x y π w := P₁.inD hI hJ A hwm₁ hyw
  obtain ⟨ℓ, hℓ⟩ := c.exists_adjLine x
  obtain ⟨hxl, hwl⟩ := hℓ w hwD.1
  obtain ⟨w₂, hw₂m₂, hw₂l⟩ := (hO₂ (ℓ w) hxl).2 ((hO₁ (ℓ w) hxl).1 ⟨w, hwm₁, hwl⟩)
  have hyw₂ : c.Delta.Adj y w₂ := ρ.adj_of_inD_on_line hI hJ S A P₂ hw₂m₂ hxl hw₂l hwD hwl
  have hww₂ : w = w₂ :=
    c.rh21_eq_of_onL hI hJ (S.triple d A.inD).1 (S.triple d A.inD).2 hxl hwl hw₂l hyw hyw₂
  rw [← hww₂] at hw₂m₂
  exact hne (c.eq_of_onL hI.lineU hJ hwd hwm₁ P₁.on_d hw₂m₂ P₂.on_d)

include ρ in
theorem card_inter_discTrios (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1}
    {π : G ⧸ c.G3} {d : G ⧸ c.G1} {L M m : G ⧸ c.G2} (S : c.DiscData x y π)
    (A : c.AtPt x y π d L M) (P : c.PenLine π d L M m) {g : G} (hg : g • c.x0 = x)
    {O : Finset (Finset (Finset (Fin 24)))}
    (hO : ∀ n, c.OnL x n → ((∃ w, c.OnL w m ∧ c.OnL w n) ↔ ρ.trio (g⁻¹ • n) ∈ O)) :
    (O ∩ ρ.discTrios x y π g).card = 3 := by
  have h5 : ∀ w, c.OnL w m → c.Delta.Adj x w := fun w hw => P.adj_x hI hJ A hw
  have hxm : ¬ c.OnL x m := P.not_onL_x hI hJ A
  obtain ⟨ℓ, hℓ⟩ := ρ.exists_lines_at hI hJ hg S.x_on P.lnP
  have hA := P.ncard_y hI hJ A
  have hinj : Set.InjOn (fun w => ρ.trio (g⁻¹ • ℓ w)) {w | c.OnL w m ∧ c.Delta.Adj y w} := by
    rintro w ⟨hwm, -⟩ w' ⟨hw'm, -⟩ h
    by_contra hne
    obtain ⟨hxl, hwl, -⟩ := hℓ w hwm (h5 w hwm)
    obtain ⟨hxl', hwl', -⟩ := hℓ w' hw'm (h5 w' hw'm)
    have hl : ℓ w = ℓ w' := ρ.eq_of_trio_at hg hxl hxl' h
    have hvn : c.OnL w' (ℓ w) := by
      rw [hl]
      exact hwl'
    exact c.not_onL_of_two_pts hI.lineU hJ hxm hwm hw'm hne hwl hvn hxl
  have hcoe : (↑(O ∩ ρ.discTrios x y π g) : Set (Finset (Finset (Fin 24)))) =
      (fun w => ρ.trio (g⁻¹ • ℓ w)) '' {w | c.OnL w m ∧ c.Delta.Adj y w} := by
    ext t
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, Set.mem_image,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨htO, htS⟩
      obtain ⟨-, n, hxn, hnπ, rfl, w', hw', hw'n⟩ := (ρ.mem_discTrios).1 htS
      obtain ⟨w, hwm, hwn⟩ := (hO n hxn).2 htO
      have hyw : c.Delta.Adj y w := ρ.adj_of_inD_on_line hI hJ S A P hwm hxn hwn hw' hw'n
      obtain ⟨-, -, -, -, huniq⟩ := hℓ w hwm (h5 w hwm)
      exact ⟨w, ⟨hwm, hyw⟩, by rw [huniq n hxn hwn]⟩
    · rintro ⟨w, ⟨hwm, hyw⟩, rfl⟩
      obtain ⟨hxl, hwl, hlπ, hmem, -⟩ := hℓ w hwm (h5 w hwm)
      exact ⟨(hO (ℓ w) hxl).1 ⟨w, hwm, hwl⟩, (ρ.mem_discTrios).2 ⟨hmem, ℓ w, hxl, hlπ, rfl, w,
        P.inD hI hJ A hwm hyw, hwl⟩⟩
  rw [← Set.ncard_coe_finset, hcoe, Set.InjOn.ncard_image hinj, hA]

include ρ in
theorem exists_two_spreads (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y : G ⧸ c.G1}
    {π : G ⧸ c.G3} (S : c.DiscData x y π) {g : G} (hg : g • c.x0 = x)
    {k : Finset (Finset (Fin 24))} (hk : k ∈ ρ.discTrios x y π g) :
    ∃ O₁ ∈ M24G.spreadsOf (ρ.sext (g⁻¹ • π)), ∃ O₂ ∈ M24G.spreadsOf (ρ.sext (g⁻¹ • π)),
      O₁ ≠ O₂ ∧ k ∈ O₁ ∧ k ∈ O₂ ∧ (O₁ ∩ ρ.discTrios x y π g).card = 3 ∧
        (O₂ ∩ ρ.discTrios x y π g).card = 3 := by
  obtain ⟨-, n, hxn, hnπ, rfl, d, hd, hdn⟩ := (ρ.mem_discTrios).1 hk
  obtain ⟨M, hdM, hyM⟩ := c.exists_onL_of_adj hd.2.1.symm
  have A : c.AtPt x y π d n M := ⟨hd, hdn, hxn, hdM, hyM⟩
  obtain ⟨m₁, m₂, hne, P₁, P₂⟩ := ρ.exists_two_lines hI hJ S A
  obtain ⟨O₁, hO₁, hO₁p⟩ := ρ.stmt7_3_two hI hJ hg S.x_on P₁.lnP (P₁.not_onL_x hI hJ A)
    fun w hw => P₁.adj_x hI hJ A hw
  obtain ⟨O₂, hO₂, hO₂p⟩ := ρ.stmt7_3_two hI hJ hg S.x_on P₂.lnP (P₂.not_onL_x hI hJ A)
    fun w hw => P₂.adj_x hI hJ A hw
  exact ⟨O₁, hO₁, O₂, hO₂, ρ.spread_ne hI hJ S A P₁ P₂ hne hO₁p hO₂p,
    (hO₁p n hxn).1 ⟨d, P₁.on_d, hdn⟩, (hO₂p n hxn).1 ⟨d, P₂.on_d, hdn⟩,
    ρ.card_inter_discTrios hI hJ S A P₁ hg hO₁p, ρ.card_inter_discTrios hI hJ S A P₂ hg hO₂p⟩

include ρ in
theorem ncard_inDeltaP_le (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) : {d | c.InDeltaP x y π d}.ncard ≤ 7 := by
  obtain ⟨hxu, huy, -⟩ := c.rh21_path h2 h1
  have hδ3 : M ∈ c.deltaAt 3 u L := c.rh21_mem_delta3 hI hJ h2 h1 hLu hLx hMu hMy
  obtain ⟨a, b, e, -, -, -, hT⟩ :=
    Set.ncard_eq_three.1 (ρ.ncard_delta_one_of_meetsP hLu hMu hδ3 hπu hLπ hMπ)
  obtain ⟨A, hAdef⟩ : ∃ A : G ⧸ c.G2 → Set (G ⧸ c.G1),
      ∀ N, A N = {w | c.OnL w N ∧ c.Delta.Adj y w} \ {u} := ⟨fun N => _, fun N => rfl⟩
  have hA : ∀ N, N ∈ c.deltaAt 1 u M → c.OnL u N → (A N).ncard = 2 := by
    intro N hNM hN
    have hu : u ∈ {w | c.OnL w N ∧ c.Delta.Adj y w} := ⟨hN, huy.symm⟩
    rw [hAdef, Set.ncard_sdiff_singleton_of_mem hu,
      c.stmt7_1_one hI.s54 hJ hMu hMy huy.ne.symm hNM]
  have hTmem : ∀ N, (c.OnL u N ∧ c.LnP N π ∧ N ∈ c.deltaAt 1 u M) ↔ (N = a ∨ N = b ∨ N = e) := by
    intro N
    simpa using Set.ext_iff.1 hT N
  have ha := (hTmem a).2 (Or.inl rfl)
  have hb := (hTmem b).2 (Or.inr (Or.inl rfl))
  have he := (hTmem e).2 (Or.inr (Or.inr rfl))
  have hsub : {d | c.InDeltaP x y π d} ⊆ {u} ∪ (A a ∪ A b ∪ A e) := by
    intro d hd
    by_cases hdu : d = u
    · exact Or.inl hdu
    · right
      have hud : c.Delta.Adj u d :=
        c.rh21_clique hI hJ h2 h1 ⟨hxu, huy.symm, hπu⟩ hd (Ne.symm hdu)
      obtain ⟨N, hNu, hNd⟩ := c.exists_onL_of_adj hud
      obtain ⟨hNπ, hNM⟩ :=
        ρ.line_mem_delta_one hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd hdu hNu hNd
      have hmemd : d ∈ A N := by
        rw [hAdef]
        exact ⟨⟨hNd, hd.2.1⟩, hdu⟩
      rcases (hTmem N).1 ⟨hNu, hNπ, hNM⟩ with rfl | rfl | rfl
      · exact Or.inl (Or.inl hmemd)
      · exact Or.inl (Or.inr hmemd)
      · exact Or.inr hmemd
  have hc1 := Set.ncard_union_le ({u} : Set (G ⧸ c.G1)) (A a ∪ A b ∪ A e)
  have hc2 := Set.ncard_union_le (A a ∪ A b) (A e)
  have hc3 := Set.ncard_union_le (A a) (A b)
  rw [Set.ncard_singleton] at hc1
  have hca := hA a ha.2.2 ha.1
  have hcb := hA b hb.2.2 hb.1
  have hce := hA e he.2.2 he.1
  have hc4 := Set.ncard_le_ncard hsub
  omega

include ρ in
theorem card_discTrios_le (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) (g : G) :
    (ρ.discTrios x y π g).card ≤ 7 := by
  obtain ⟨ℓ, hℓ⟩ := c.exists_adjLine x
  have hD := ρ.ncard_inDeltaP_le hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ
  have hsub : (↑(ρ.discTrios x y π g) : Set (Finset (Finset (Fin 24)))) ⊆
      (fun d => ρ.trio (g⁻¹ • ℓ d)) '' {d | c.InDeltaP x y π d} := by
    intro t ht
    obtain ⟨-, n, hxn, -, rfl, w, hw, hwn⟩ := (ρ.mem_discTrios).1 (Finset.mem_coe.1 ht)
    obtain ⟨hxl, hwl⟩ := hℓ w hw.1
    refine ⟨w, hw, ?_⟩
    have hn : n = ℓ w := c.eq_of_onL hI.lineU hJ hw.1.ne hxn hwn hxl hwl
    rw [hn]
  calc (ρ.discTrios x y π g).card
      = (↑(ρ.discTrios x y π g) : Set (Finset (Finset (Fin 24)))).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ ((fun d => ρ.trio (g⁻¹ • ℓ d)) '' {d | c.InDeltaP x y π d}).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ {d | c.InDeltaP x y π d}.ncard := Set.ncard_image_le
    _ ≤ 7 := hD

end Five

section Six


include ρ in
theorem inD_triple (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) {d : G ⧸ c.G1} (hd : c.InDeltaP x y π d) :
    c.Rh 2 x d y ∧ ¬ c.Rh 1 x d y := by
  by_cases hdu : d = u
  · rw [hdu]
    exact ⟨h2, h1⟩
  · obtain ⟨hxu, huy, -⟩ := c.rh21_path h2 h1
    have hud : c.Delta.Adj u d :=
      c.rh21_clique hI hJ h2 h1 ⟨hxu, huy.symm, hπu⟩ hd (Ne.symm hdu)
    obtain ⟨N, hNu, hNd⟩ := c.exists_onL_of_adj hud
    obtain ⟨-, hNM⟩ :=
      ρ.line_mem_delta_one hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd hdu hNu hNd
    exact ρ.claimA hI hJ h2 h1 hd.1 hud hd.2.1 hLu hLx hMu hMy hNu hNd
      (ρ.line_mem_delta_one_or_two hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd hdu hNu hNd) hNM

include ρ in
theorem discData_of (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1}
    (h2 : c.Rh 2 x u y) (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L)
    (hLx : c.OnL x L) (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π)
    (hLπ : c.LnP L π) (hMπ : c.MeetsP u M π) : c.DiscData x y π :=
  ⟨c.inc_pt_plane hLx hLπ,
    fun _ hd => ρ.inD_triple hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd,
    fun _ _ hd hdM hyM => ρ.inD_meetsP hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ hd hdM hyM⟩

theorem stmt7_4_one (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y : G ⧸ c.G1} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) {L M : G ⧸ c.G2} (hLu : c.OnL u L) (hLx : c.OnL x L)
    (hMu : c.OnL u M) (hMy : c.OnL y M) {π : G ⧸ c.G3} (hπu : c.OnP u π) (hLπ : c.LnP L π)
    (hMπ : c.MeetsP u M π) {g : G} (hg : g • c.x0 = x) :
    ∃ d ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)), ∀ n, c.OnL x n → c.LnP n π →
      ((∃ w, c.Delta.Adj x w ∧ c.Delta.Adj y w ∧ c.OnP w π ∧ c.OnL w n) ↔
        (ρ.trio (g⁻¹ • n) ≠ d ∧ ¬ Disjoint (ρ.trio (g⁻¹ • n)) d)) := by
  obtain ⟨hxu, huy, -⟩ := c.rh21_path h2 h1
  have S : c.DiscData x y π := ρ.discData_of hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg S.x_on
  have hSP : ρ.discTrios x y π g ⊆ M24G.triosOf (ρ.sext (g⁻¹ • π)) := fun t ht =>
    ((ρ.mem_discTrios).1 ht).1
  have hne : (ρ.discTrios x y π g).Nonempty :=
    ⟨ρ.trio (g⁻¹ • L), (ρ.trio_mem_discTrios_iff hg S.x_on hLx hLπ).2
      ⟨u, ⟨hxu, huy.symm, hπu⟩, hLu⟩⟩
  have h3 := M24G.card_inter_eq_three hU hSP fun k hk => ρ.exists_two_spreads hI hJ S hg hk
  have hle := ρ.card_discTrios_le hI hJ h2 h1 hLu hLx hMu hMy hπu hLπ hMπ g
  rcases M24G.stmt2_2_triosOf hU hSP hne h3 with ⟨d, hd, hSd, -, -⟩ | h9
  · refine ⟨d, hd, fun n hxn hnπ => ?_⟩
    have key : (∃ w, c.Delta.Adj x w ∧ c.Delta.Adj y w ∧ c.OnP w π ∧ c.OnL w n) ↔
        ρ.trio (g⁻¹ • n) ∈ ρ.discTrios x y π g := by
      rw [ρ.trio_mem_discTrios_iff hg S.x_on hxn hnπ]
      simp only [Loc49.InDeltaP, and_assoc]
    rw [key, hSd, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨ρ.trio_mem_triosOf hg S.x_on hxn hnπ, h⟩⟩
  · omega

end Six

end ResM24

end CFSG.Quasithin.H13.AS91
