module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaBasic

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

private theorem exists_smul_of_delta_of_base (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (hM : MoufangCondition c.G0 c.graph n)
    {p : GPath (delta c Good n) n} (hp : p.NoBack)
    (hbase : (p (n - 1) = deltaXv c n ∧ p n = deltaLv c n) ∨
      (p (n - 1) = deltaLv c n ∧ p n = deltaXv c n))
    {y y' : ↥(edgeBall (n - 1) c)}
    (hy : (delta c Good n).Adj (p n) y)
    (hy' : (delta c Good n).Adj (p n) y')
    (hne : y ≠ p (n - 1)) (hne' : y' ≠ p (n - 1)) :
    ∃ k : ↥(deltaGroup hn hgirth hG hdeg),
      (∀ i, 1 ≤ i → i ≤ n - 1 → ∀ w, (delta c Good n).Adj (p i) w → k • w = w) ∧
        k • y = y' := by
  have hheight_pnm1 : height c ((p (n - 1)) : c.Γ) = 0 := by
    rcases hbase with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]
      simp [height, deltaXv]
    · rw [h1]
      simp [height, deltaLv]
  have hheight_pn : height c ((p n) : c.Γ) = 0 := by
    rcases hbase with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2]
      simp [height, deltaLv]
    · rw [h2]
      simp [height, deltaXv]
  have hheight : ∀ i, i ≤ n - 1 → height c ((p i) : c.Γ) ≤ n - 1 - i := by
    have key : ∀ k, k ≤ n - 1 → height c ((p (n - 1 - k)) : c.Γ) ≤ k := by
      intro k
      induction k with
      | zero => intro _; simpa using hheight_pnm1
      | succ k ih =>
        intro hk
        have hk' : k ≤ n - 1 := by omega
        have hstep : height c ((p (n - 1 - (k + 1))) : c.Γ) ≤
            height c ((p (n - 1 - k)) : c.Γ) + 1 := by
          have hidx : n - 1 - (k + 1) < n := by omega
          have hadj : (delta c Good n).Adj (p (n - 1 - (k + 1))) (p (n - 1 - k)) := by
            have h := p.adj (n - 1 - (k + 1)) hidx
            rwa [show n - 1 - (k + 1) + 1 = n - 1 - k by omega] at h
          exact height_le_succ_of_delta_adj hn hgirth hG
            (u := p (n - 1 - k)) (v := p (n - 1 - (k + 1))) hadj.symm
        have hik := ih hk'
        omega
    intro i hi
    have h := key (n - 1 - i) (by omega)
    rwa [show n - 1 - (n - 1 - i) = i by omega] at h
  have hheight_le : ∀ i, 1 ≤ i → i ≤ n - 1 → height c ((p i) : c.Γ) ≤ n - 2 := by
    intro i hi1 hi2
    have h := hheight i hi2
    omega
  have hheight_le_n : height c ((p n) : c.Γ) ≤ n - 2 := by
    have h := hheight_pn
    omega
  have hgamma : ∀ i, i < n → c.graph.Adj ((p i) : c.Γ) ((p (i + 1)) : c.Γ) := by
    intro i hi
    have hh : height c ((p (i + 1)) : c.Γ) ≤ n - 2 := by
      rcases Nat.lt_or_ge (i + 1) n with hlt | hge
      · exact hheight_le (i + 1) (by omega) (by omega)
      · have hEq : i + 1 = n := by omega
        rw [hEq]
        exact hheight_le_n
    have hadj : (delta c Good n).Adj (p (i + 1)) (p i) := (p.adj i hi).symm
    exact ((delta_adj_iff_of_height_le hn hgirth hG (u := p (i + 1)) (v := p i) hh).mp
      hadj).symm
  let q : GPath c.graph n :=
    { toFun := fun i => ((p i) : c.Γ)
      adj := fun i hi => hgamma i hi
      tail := fun i hi => congrArg Subtype.val (p.tail i hi) }
  have hqnb : q.NoBack := by
    intro i hi h
    exact hp i hi (Subtype.ext (by simpa [q] using h))
  have hqy : c.graph.Adj (q n) (y : c.Γ) :=
    (delta_adj_iff_of_height_le hn hgirth hG (u := p n) (v := y) hheight_le_n).mp hy
  have hqy' : c.graph.Adj (q n) (y' : c.Γ) :=
    (delta_adj_iff_of_height_le hn hgirth hG (u := p n) (v := y') hheight_le_n).mp hy'
  have hqne : (y : c.Γ) ≠ q (n - 1) := by
    intro h
    exact hne (Subtype.ext (by simpa [q] using h))
  have hqne' : (y' : c.Γ) ≠ q (n - 1) := by
    intro h
    exact hne' (Subtype.ext (by simpa [q] using h))
  obtain ⟨a, hafix, hay⟩ := hM q hqnb (y : c.Γ) (y' : c.Γ) hqy hqy' hqne hqne'
  have hfix_pnm1 : a • ((p (n - 1)) : c.Γ) = ((p (n - 1)) : c.Γ) := by
    have hadj : c.graph.Adj (q (n - 2)) ((p (n - 1)) : c.Γ) := by
      have h := hgamma (n - 2) (by omega)
      rwa [show n - 2 + 1 = n - 1 by omega] at h
    exact hafix (n - 2) (by omega) (by omega) ((p (n - 1)) : c.Γ) hadj
  have hfix_pn : a • ((p n) : c.Γ) = ((p n) : c.Γ) := by
    have hadj : c.graph.Adj (q (n - 1)) ((p n) : c.Γ) := by
      have h := hgamma (n - 1) (by omega)
      rwa [show n - 1 + 1 = n by omega] at h
    exact hafix (n - 1) (by omega) (le_refl _) ((p n) : c.Γ) hadj
  have ha_xv : a • c.xv = c.xv := by
    rcases hbase with ⟨h1, -⟩ | ⟨-, h2⟩
    · have h1' : ((p (n - 1)) : c.Γ) = c.xv := congrArg Subtype.val h1
      rw [← h1']
      exact hfix_pnm1
    · have h2' : ((p n) : c.Γ) = c.xv := congrArg Subtype.val h2
      rw [← h2']
      exact hfix_pn
  have ha_lv : a • c.lv = c.lv := by
    rcases hbase with ⟨-, h2⟩ | ⟨h1, -⟩
    · have h2' : ((p n) : c.Γ) = c.lv := congrArg Subtype.val h2
      rw [← h2']
      exact hfix_pn
    · have h1' : ((p (n - 1)) : c.Γ) = c.lv := congrArg Subtype.val h1
      rw [← h1']
      exact hfix_pnm1
  let e : ↥(MulAction.stabilizer c.G0 c.xv) := ⟨a, MulAction.mem_stabilizer_iff.mpr ha_xv⟩
  let k : ↥(deltaGroup hn hgirth hG hdeg) :=
    ⟨hatXHom hn hgirth hG hdeg e, Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)⟩
  refine ⟨k, ?_, ?_⟩
  · intro i hi1 hi2 w hw
    have hheight_i : height c ((p i) : c.Γ) ≤ n - 2 := hheight_le i hi1 hi2
    have hwgamma : c.graph.Adj ((p i) : c.Γ) (w : c.Γ) :=
      (delta_adj_iff_of_height_le hn hgirth hG (u := p i) (v := w) hheight_i).mp hw
    have haw : a • (w : c.Γ) = (w : c.Γ) :=
      hafix i hi1 hi2 (w : c.Γ) (by simpa [q] using hwgamma)
    have hk : (k : Equiv.Perm ↥(edgeBall (n - 1) c)) w = w := by
      change hatX hn hgirth hG e w = w
      apply Subtype.ext
      rw [hatX_of_smul_eq hn hgirth hG e ha_lv w]
      exact haw
    simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using hk
  · have hk : (k : Equiv.Perm ↥(edgeBall (n - 1) c)) y = y' := by
      change hatX hn hgirth hG e y = y'
      apply Subtype.ext
      rw [hatX_of_smul_eq hn hgirth hG e ha_lv y]
      exact hay
    simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using hk

theorem moufangCondition_delta (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (hM : MoufangCondition c.G0 c.graph n) :
    MoufangCondition ↥(deltaGroup hn hgirth hG hdeg) (delta c Good n) n := by
  intro p hp y y' hy hy' hne hne'
  have hp_edge : (delta c Good n).Adj (p (n - 1)) (p n) := by
    have h := p.adj (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega] at h
  obtain ⟨g, hg⟩ := exists_smul_eq_base_of_adj hn hgirth hG hdeg hp_edge
  have hbase : ((g • p) (n - 1) = deltaXv c n ∧ (g • p) n = deltaLv c n) ∨
      ((g • p) (n - 1) = deltaLv c n ∧ (g • p) n = deltaXv c n) := by
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simpa using h1, by simpa using h2⟩
    · exact Or.inr ⟨by simpa using h1, by simpa using h2⟩
  have hy1 : (delta c Good n).Adj ((g • p) n) (g • y) := by
    have h := ((graphAction_deltaGroup hn hgirth hG hdeg).adj_smul g (p n) y).mpr hy
    simpa using h
  have hy2 : (delta c Good n).Adj ((g • p) n) (g • y') := by
    have h := ((graphAction_deltaGroup hn hgirth hG hdeg).adj_smul g (p n) y').mpr hy'
    simpa using h
  have hinj : Function.Injective (fun z : ↥(edgeBall (n - 1) c) => g • z) := by
    intro z1 z2 h
    have := congrArg (fun z => g⁻¹ • z) h
    simpa [← mul_smul] using this
  have hne1 : (g • y : ↥(edgeBall (n - 1) c)) ≠ (g • p) (n - 1) := by
    have h : g • y ≠ g • p (n - 1) := fun heq => hne (hinj heq)
    simpa using h
  have hne2 : (g • y' : ↥(edgeBall (n - 1) c)) ≠ (g • p) (n - 1) := by
    have h : g • y' ≠ g • p (n - 1) := fun heq => hne' (hinj heq)
    simpa using h
  obtain ⟨k, hkfix, hky⟩ :=
    exists_smul_of_delta_of_base hn hgirth hG hdeg hM (GPath.smul_noBack (g := g) hp)
      hbase hy1 hy2 hne1 hne2
  refine ⟨g⁻¹ * k * g, ?_, ?_⟩
  · intro i hi1 hi2 w hw
    have hw' : (delta c Good n).Adj ((g • p) i) (g • w) := by
      have h := ((graphAction_deltaGroup hn hgirth hG hdeg).adj_smul g (p i) w).mpr hw
      simpa using h
    have hfix := hkfix i hi1 hi2 (g • w) hw'
    calc (g⁻¹ * k * g) • w = g⁻¹ • (k • (g • w)) := by rw [mul_smul, mul_smul]
      _ = g⁻¹ • (g • w) := by rw [hfix]
      _ = w := by rw [← mul_smul, inv_mul_cancel, one_smul]
  · calc (g⁻¹ * k * g) • y = g⁻¹ • (k • (g • y)) := by rw [mul_smul, mul_smul]
      _ = g⁻¹ • (g • y') := by rw [hky]
      _ = y' := by rw [← mul_smul, inv_mul_cancel, one_smul]

end CFSG.Quasithin.Stroth.WeissDelta

end
