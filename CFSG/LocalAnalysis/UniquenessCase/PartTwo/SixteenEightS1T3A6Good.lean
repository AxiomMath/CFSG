module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarPt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6Trans
public import CFSG.GroupTheory.AlternatingThreeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_fixV_map_iff {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {g : MulAut W} (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W))) (w : W) :
    g w ∈ fixV H ↔ w ∈ fixV H := by
  have hconj : ∀ x : MulAut W, x ∈ H ↔ g * x * g⁻¹ ∈ H :=
    Subgroup.mem_normalizer_iff.mp hg
  have hinv : ∀ x : MulAut W, x ∈ H ↔ g⁻¹ * x * g ∈ H :=
    Subgroup.mem_normalizer_iff''.mp hg
  constructor
  · intro hw x hx
    have h1 : g * x * g⁻¹ ∈ H := (hconj x).mp hx
    have h2 := hw (g * x * g⁻¹) h1
    have h3 : g (x w) = g w := by
      calc g (x w) = (g * x * g⁻¹) (g w) := by simp [MulAut.mul_apply]
        _ = g w := h2
    exact g.injective h3
  · intro hw x hx
    have h1 : g⁻¹ * x * g ∈ H := (hinv x).mp hx
    have h2 := hw (g⁻¹ * x * g) h1
    calc x (g w) = g ((g⁻¹ * x * g) w) := by simp [MulAut.mul_apply]
      _ = g w := by rw [h2]

theorem ThreeNat.exists_fixed_vector_alt_six
    {W : Type} [CommGroup W] [Finite W]
    {A H T : Subgroup (MulAut W)}
    (h : ThreeNat A H T)
    (h7 : Nat.card ↥(irrSet H) = 7)
    (hA6 : UC22.IsAlt ↥H 6)
    (hK : Nat.card ↥(s1t3KBar A H) = 168) :
    ∃ w : W, w ≠ 1 ∧ w ∈ fixV T ∧
      ∃ E : Subgroup (MulAut W), E ≤ A ∧ IsPGroup 3 ↥E ∧
        ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  classical
  have hTp : IsPGroup 2 T := h.sylow.isPGroup
  by_cases hfix : fixV (H) = ⊥
  ·
    obtain ⟨I₀, hI₀, hI₀T, J₂, hJ₂le, -, hJ₂mem, hJ₂card, -⟩ :=
      h.exists_point_stabilizer h7 hK
    have hI₀nat : SumOfNatShape (H) I₀
        (I₀ ⊓ fixV (H)) 1 := h.natural_of_mem_irrSet hI₀
    have hnat := s16t3_alt6_natural h.quasi hA6 hI₀nat
    have hI₀fix : I₀ ⊓ fixV (H) = ⊥ := by rw [hfix, inf_bot_eq]
    have hcardI : Nat.card ↥I₀ = 16 := by
      have h1 := hnat.1
      rw [hI₀fix, Subgroup.card_bot, mul_one] at h1
      exact h1
    have hI₀ne : I₀ ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥I₀ = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hcardI] at h1
      norm_num at h1
    obtain ⟨w, hwI, hw1, hwfixT⟩ :=
      s15_Lin_exists_ne_one_mem_fixV hTp (fun w => by rw [pow_two]; exact h.elem w) hI₀ne hI₀T
    letI : MulAction ↥(H) ↥I₀ :=
      { smul := fun l x => ⟨(l : MulAut (W)) (x : W),
            hI₀.2.2.1 l l.2 x x.2⟩
        one_smul := fun x => Subtype.ext rfl
        mul_smul := fun l m x => Subtype.ext rfl }
    haveI : Fintype ↥I₀ := Fintype.ofFinite _
    haveI : Fintype ↥(H) := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit ↥(H) (⟨w, hwI⟩ : ↥I₀)) :=
      Fintype.ofFinite _
    haveI : Fintype (MulAction.stabilizer ↥(H) (⟨w, hwI⟩ : ↥I₀)) :=
      Fintype.ofFinite _
    have horbit : MulAction.orbit ↥(H) (⟨w, hwI⟩ : ↥I₀) =
        {x : ↥I₀ | x ≠ 1} := by
      ext x
      constructor
      · rintro ⟨l, rfl⟩ hx1
        apply hw1
        have hthis : ((l • (⟨w, hwI⟩ : ↥I₀) : ↥I₀) : W) = 1 :=
          congrArg Subtype.val hx1
        have h2 : (l : MulAut (W)) w = 1 := by
          change ((l • (⟨w, hwI⟩ : ↥I₀) : ↥I₀) : W) = 1
          exact hthis
        exact (l : MulAut (W)).injective (by rw [h2, map_one])
      · intro hx1
        have hxne : (x : W) ≠ 1 := fun h => hx1 (Subtype.ext h)
        have hwnf : w ∉ fixV (H) := by
          rw [hfix]; exact fun h => hw1 (Subgroup.mem_bot.mp h)
        have hxnf : (x : W) ∉ fixV (H) := by
          rw [hfix]; exact fun h => hxne (Subgroup.mem_bot.mp h)
        obtain ⟨l, hl, hlw⟩ := hnat.2 w hwI hwnf (x : W) x.2 hxnf
        refine ⟨⟨l, hl⟩, ?_⟩
        apply Subtype.ext
        have h1 : l w * (x : W)⁻¹ = 1 := by
          rw [hfix] at hlw
          exact Subgroup.mem_bot.mp hlw
        show l w = (x : W)
        exact mul_inv_eq_one.mp h1
    have hcardOrbit : Nat.card (MulAction.orbit ↥(H)
        (⟨w, hwI⟩ : ↥I₀)) = 15 := by
      rw [horbit]
      change Nat.card {x : ↥I₀ // x ≠ 1} = 15
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : ↥I₀ => x = 1),
        Fintype.card_subtype_eq (1 : ↥I₀), ← Nat.card_eq_fintype_card, hcardI]
    have hLcard : Nat.card ↥(H) = 360 := by
      obtain ⟨e'⟩ := hA6
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hOS' : Nat.card (MulAction.orbit ↥(H) (⟨w, hwI⟩ : ↥I₀)) *
        Nat.card (MulAction.stabilizer ↥(H) (⟨w, hwI⟩ : ↥I₀)) =
        Nat.card ↥(H) := by
      have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (G := ↥(H)) (⟨w, hwI⟩ : ↥I₀)
      simpa only [Nat.card_eq_fintype_card] using hOS
    have hstab3 : 3 ∣ Nat.card (MulAction.stabilizer ↥(H)
        (⟨w, hwI⟩ : ↥I₀)) := by
      have h1 := hOS'
      rw [hcardOrbit, hLcard] at h1
      have h2 : Nat.card (MulAction.stabilizer ↥(H)
          (⟨w, hwI⟩ : ↥I₀)) = 24 := by omega
      rw [h2]
      norm_num
    obtain ⟨c', hc'order⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(MulAction.stabilizer ↥(H) (⟨w, hwI⟩ : ↥I₀))) 3 hstab3
    let c : MulAut (W) := (c' : ↥(H))
    have hcL : c ∈ H := (c' : ↥(H)).2
    have hcorder : orderOf c = 3 := by
      simp only [c, Subgroup.orderOf_coe, hc'order]
    have hcw : c w = w := by
      have hfix' := MulAction.mem_stabilizer_iff.mp c'.2
      change ((c' • (⟨w, hwI⟩ : ↥I₀) : ↥I₀) : W) = w
      exact congrArg Subtype.val hfix'
    have h3dvdJ₂ : 3 ∣ Nat.card ↥J₂ := by
      rw [hJ₂card]
      exact dvd_mul_right 3 _
    obtain ⟨k2, hk2order⟩ := exists_prime_orderOf_dvd_card' (G := ↥J₂) 3 h3dvdJ₂
    let κ : MulAut (W) := (k2 : MulAut (W))
    have hκJ₂ : κ ∈ J₂ := k2.2
    have hκKbar : κ ∈ s1t3KBar (A) (H) := hJ₂le hκJ₂
    have hκorder : orderOf κ = 3 := by
      simp only [κ, Subgroup.orderOf_coe, hk2order]
    have hκI₀ : I₀.map κ.toMonoidHom = I₀ := (hJ₂mem κ hκKbar).1 hκJ₂
    have hκnorm : κ ∈ Subgroup.normalizer
        (H : Set (MulAut (W))) :=
      h.normal (Subgroup.mem_inf.mp hκKbar).1
    have hfixκ : ∀ u : W, κ u ∈ fixV (H) ↔
        u ∈ fixV (H) := by
      intro u
      constructor
      · intro hu l hl
        have hcomm : l * κ = κ * l :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hκKbar).2) l hl
        have h1 : l (κ u) = κ (l u) := by
          have := congrArg (fun m : MulAut (W) => m u) hcomm
          simpa [MulAut.mul_apply] using this
        exact κ.injective (h1.symm.trans (hu l hl))
      · intro hu l hl
        have hcomm : l * κ = κ * l :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hκKbar).2) l hl
        have h1 : l (κ u) = κ (l u) := by
          have := congrArg (fun m : MulAut (W) => m u) hcomm
          simpa [MulAut.mul_apply] using this
        exact h1.trans (congrArg κ (hu l hl))
    let φ : ↥I₀ ≃* ↥I₀ :=
      (MulEquiv.subgroupMap κ I₀).trans (MulEquiv.subgroupCongr hκI₀)
    have hφapply : ∀ u : ↥I₀,
        ((φ u : ↥I₀) : W) = κ (u : W) := by
      intro u
      rfl
    have hZ : ∀ u : ↥I₀, ((φ u : ↥I₀) : W) ∈
        I₀ ⊓ fixV (H) ↔
        (u : W) ∈ I₀ ⊓ fixV (H) := by
      intro u
      constructor
      · intro hmem
        refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
        have h1 := (Subgroup.mem_inf.mp hmem).2
        rw [hφapply u] at h1
        exact (hfixκ (u : W)).1 h1
      · intro hmem
        refine Subgroup.mem_inf.mpr ⟨(φ u).2, ?_⟩
        rw [hφapply u]
        exact (hfixκ (u : W)).2 (Subgroup.mem_inf.mp hmem).2
    have hφE : ∀ l ∈ H, ∀ u : ↥I₀,
        ∀ hu : l (u : W) ∈ I₀,
        ((φ ⟨l (u : W), hu⟩ : ↥I₀) : W) *
          (l ((φ u : ↥I₀) : W))⁻¹ ∈
          I₀ ⊓ fixV (H) := by
      intro l hl u hu
      have hcent : l * κ = κ * l :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hκKbar).2) l hl
      have hstep : κ (l (u : W)) = l (κ (u : W)) := by
        have h1 : l (κ (u : W)) = κ (l (u : W)) := by
          have := congrArg (fun m : MulAut (W) =>
            m (u : W)) hcent
          simpa [MulAut.mul_apply] using this
        exact h1.symm
      rw [Subgroup.mem_inf]
      constructor
      · rw [hφapply, hφapply, hstep, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [hφapply, hφapply, hstep, mul_inv_cancel]
        exact Subgroup.one_mem _
    have hκw : κ w = w := by
      have heq := SumOfNatShape.eq_of_equivariant h.quasi hI₀nat φ hZ hφE
        (⟨w, hwI⟩ : ↥I₀)
      rw [hI₀fix, Subgroup.mem_bot] at heq
      have h2 : ((φ ⟨w, hwI⟩ : ↥I₀) : W) = w := mul_inv_eq_one.mp heq
      rw [← hφapply (⟨w, hwI⟩ : ↥I₀)]
      exact h2
    have hcκ : Commute c κ :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hκKbar).2) c hcL
    let E : Subgroup (MulAut (W)) :=
      Subgroup.zpowers c ⊔ Subgroup.zpowers κ
    have hEp : IsPGroup 3 ↥E := by
      have hHp : IsPGroup 3 ↥(Subgroup.zpowers c) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcorder, pow_one])
      have hKp : IsPGroup 3 ↥(Subgroup.zpowers κ) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hκorder, pow_one])
      have hHK : Subgroup.zpowers c ≤ Subgroup.normalizer
          (Subgroup.zpowers κ : Set (MulAut (W))) := by
        rw [Subgroup.zpowers_le]
        refine (Subgroup.centralizer_le_normalizer _) ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hcκ.zpow_right n).symm
      exact hHp.to_sup_of_normal_right' hKp hHK
    have hEcc : ¬ IsCyclic ↥E := by
      intro hcyc
      haveI : IsCyclic ↥E := hcyc
      have hcE : c ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      have hκE : κ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers κ)
      have hc3 : Nat.card ↥(Subgroup.zpowers (⟨c, hcE⟩ : ↥E)) = 3 := by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, hcorder]
      have hκ3 : Nat.card ↥(Subgroup.zpowers (⟨κ, hκE⟩ : ↥E)) = 3 := by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, hκorder]
      have hzeq : Subgroup.zpowers (⟨c, hcE⟩ : ↥E) =
          Subgroup.zpowers (⟨κ, hκE⟩ : ↥E) := by
        rw [IsCyclic.subgroup_eq_iff_card_eq, hc3, hκ3]
      have hmap : Subgroup.zpowers c = Subgroup.zpowers κ := by
        have h1 := congrArg (Subgroup.map (Subgroup.subtype E)) hzeq
        simpa only [MonoidHom.map_zpowers, Subgroup.subtype_apply] using h1
      have hκL : κ ∈ H :=
        (Subgroup.zpowers_le.mpr hcL) (hmap.symm ▸ Subgroup.mem_zpowers κ)
      have hLKbot : H ⊓
          s1t3KBar (A) (H) = ⊥ := by
        obtain ⟨N, -, hLN, -, -, hNKbot, -, -⟩ := h.structure_of_seven h7
        refine le_bot_iff.mp ?_
        calc H ⊓ s1t3KBar (A) (H) ≤
              N ⊓ s1t3KBar (A) (H) :=
              inf_le_inf_right _ hLN
          _ = ⊥ := hNKbot
      have hκ1 : κ = 1 := by
        have hmem : κ ∈ H ⊓
            s1t3KBar (A) (H) :=
          Subgroup.mem_inf.mpr ⟨hκL, hκKbar⟩
        rw [hLKbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      rw [hκ1, orderOf_one] at hκorder
      norm_num at hκorder
    have hEM : E ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr (h.le hcL))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hκKbar).1)
    have hEw : ∀ e ∈ E, e w = w := by
      have hstab : E ≤ MulAction.stabilizer (MulAut (W)) w := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
          exact hcw
        · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
          exact hκw
      intro e he
      exact MulAction.mem_stabilizer_iff.mp (hstab he)
    exact ⟨w, hw1, hwfixT, E, hEM, hEp, hEcc, hEw⟩
  ·
    have hTbM : T ≤ A := h.sylow.le
    have hstab : ∀ x ∈ T, ∀ u ∈ fixV (H),
        x u ∈ fixV (H) := by
      intro x hx u hu
      exact (s16t3_fixV_map_iff (h.normal (hTbM hx)) u).2 hu
    obtain ⟨w, hwfixL, hw1, hwfixT⟩ :=
      s15_Lin_exists_ne_one_mem_fixV hTp (fun w => by rw [pow_two]; exact h.elem w) hfix hstab
    obtain ⟨P, hPp, hPnc⟩ :=
      CFSG.GroupTheory.exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup
        (X := ↥(H)) (n := 6) (by norm_num) hA6.some
    let E : Subgroup (MulAut (W)) := P.map (H).subtype
    have hEM : E ≤ A := (Subgroup.map_subtype_le P).trans h.le
    have hEp : IsPGroup 3 ↥E := hPp.map (H).subtype
    have hEc : ¬ IsCyclic ↥E := by
      intro hcyc
      haveI : IsCyclic ↥E := hcyc
      exact hPnc (isCyclic_of_injective
        (Subgroup.equivMapOfInjective P (H).subtype
          (H).subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective P (H).subtype
          (H).subtype_injective).injective)
    have hEw : ∀ e ∈ E, e w = w := by
      intro e he
      obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp he
      exact mem_fixV.mp hwfixL (p : MulAut (W)) p.2
    exact ⟨w, hw1, hwfixT, E, hEM, hEp, hEc, hEw⟩

theorem Setting16.exists_good_vector_alt6
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hset : Setting16 D V₀ V L) (h61 : UC6.R6_1 D)
    (h3 : 3 ∈ D.sig) (hV₀ : V₀ = ⊥)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hA6 : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV)
      (lBar V₀ V hV L)) = 168) :
    ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  obtain ⟨w, hw1, hwT, E, hEM, hEp, hEc, hEw⟩ :=
    hT.exists_fixed_vector_alt_six h7 hA6 hK
  obtain ⟨v, hvV, -, hvT, hvC⟩ :=
    hset.good_vector_of_fix h61 h3 hV₀ hw1
      (fun t => mem_fixV.mp hwT (t : MulAut _) t.2) hEM hEp hEc hEw
  exact ⟨v, hvV, hvT, hvC⟩

theorem S16gRowCtx.exists_good_vector_alt6 (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hV₀ : V₀ = ⊥)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M :=
  h.setting.exists_good_vector_alt6 h.std.h61 h3 hV₀ hT h7 hL hK


end CFSG.LocalAnalysis.UniquenessCase.PartTwo