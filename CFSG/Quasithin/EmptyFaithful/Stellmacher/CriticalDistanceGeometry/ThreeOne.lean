module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.CritPairs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

omit [Finite G] in
theorem le_normalizer_sup_of_conj {X A B : Subgroup G}
    (hA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ B) (hB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ A ⊔ B) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ w ∈ A ⊔ B, x * w * x⁻¹ ∈ A ⊔ B := by
    intro x hx
    have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom :=
      sup_le (fun a ha => hA x hx a ha) (fun b hb => hB x hx b hb)
    intro w hw
    exact this hw
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨key x hx w, fun hw => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hw
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_sup_of_le_normalizer {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  le_normalizer_sup_of_conj
    (fun _ hx a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hA hx) a).mp ha))
    (fun _ hx b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hB hx) b).mp hb))

omit [Finite G] in
theorem mem_normalizer_sup_of_decomp {A B Q : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.normalizer (A : Set G)) (hzQ : z ∈ Subgroup.centralizer (Q : Set G))
    (hdec : ∀ x ∈ B, ∃ a ∈ A, ∃ q ∈ Q, x = a * q) :
    z ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have := le_normalizer_sup_of_conj (X := Subgroup.zpowers z) (A := A) (B := B) ?_ ?_
  · exact this (Subgroup.mem_zpowers z)
  · intro x hx a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hn : z ^ n ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpow_mem _ hz n
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hn a).mp ha)
  · intro x hx b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨a, ha, q, hq, rfl⟩ := hdec b hb
    have hn : z ^ n ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpow_mem _ hz n
    have hnQ : z ^ n ∈ Subgroup.centralizer (Q : Set G) := Subgroup.zpow_mem _ hzQ n
    have hqc : q * z ^ n = z ^ n * q := Subgroup.mem_centralizer_iff.mp hnQ q hq
    have haa : z ^ n * a * (z ^ n)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hn a).mp ha
    have heq : z ^ n * (a * q) * (z ^ n)⁻¹ =
        (z ^ n * a * (z ^ n)⁻¹ * a⁻¹) * (a * q) := by
      have : z ^ n * q * (z ^ n)⁻¹ = q := by rw [← hqc]; group
      calc z ^ n * (a * q) * (z ^ n)⁻¹ = z ^ n * a * (z ^ n)⁻¹ * (z ^ n * q * (z ^ n)⁻¹) := by group
        _ = _ := by rw [this]; group
    rw [heq]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem (Subgroup.mem_sup_left haa)
      ((A ⊔ B).inv_mem (Subgroup.mem_sup_left ha))) (Subgroup.mem_sup_right hb)

end F53

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss31At_of_hss27S3 (hA : F53Amalgam H M S) (h27 : Hss27S3At H M) : Hss31At H M := by
  intro α β hαβ hv hα hlt
  by_contra hn
  obtain ⟨α', hc⟩ := exists_critData hA hα hαβ
  have hcomm := comm_ne_bot_of_not_central hA hc hn
  obtain ⟨hα', hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hnle := not_le_Qv_of_comm_ne hA hcomm
  have heven := hss113_d hA hc hcomm hlt
  have hvα' : vtype α' = true := by
    have := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mpr (hc.dist_eq ▸ heven)
    rw [← this]; exact hv
  have hb1 := bMin_pos hA
  have hb2 : 2 ≤ bMin H M := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hβn : β ∈ nbrs α := hαβ
  have hZαα' : Zv α ≤ stab α' :=
    Zv_le_stab_of_dist_le hA (by rw [hc.dist_eq, hc.bAt_eq])
  have hZα'β : Zv α' ≤ stab β := by
    refine Zv_le_stab_of_dist_le hA ?_
    have := hc.dist_eq'
    rw [CosetGeom.dist_comm, hα']
    omega
  obtain ⟨μ, hμn, hμβ⟩ : ∃ μ, μ ∈ nbrs α ∧ μ ≠ β := by
    have h3 := card_nbrs_true hA hv
    have : Finite (nbrs α) := Nat.finite_of_card_ne_zero (by omega)
    have : Nontrivial (nbrs α) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨μ, hμ⟩, hne⟩ := exists_ne (⟨β, hβn⟩ : nbrs α)
    exact ⟨μ, hμ, fun h => hne (Subtype.ext h)⟩
  have hαμ : (graph (H ⊔ M) H M).Adj α μ := hμn
  have hbμ : bMin H M < bAt μ := by
    have h1 : vtype α ≠ vtype μ := vtype_ne_of_adj hαμ
    have h2 : vtype α ≠ vtype β := vtype_ne_of_adj hαβ
    have hv' : vtype μ = vtype β := by
      cases h1' : vtype α <;> cases h2' : vtype μ <;> cases h3' : vtype β <;> simp_all
    rw [bAt_eq_of_vtype_eq hv']
    exact hlt
  have hdμα : dist μ α = 1 := dist_eq_one_iff_adj.mpr hαμ.symm
  have hZμQα : Zv μ ≤ Qv α := Zv_le_Qv_of_dist_lt (by omega)
  have hZμα' : Zv μ ≤ stab α' := by
    refine Zv_le_stab_of_dist_le hA ?_
    have := dist_triangle hA.amalgam.gen μ α α'
    rw [hdμα, hc.dist_eq] at this
    omega
  have hdec : ∀ x ∈ Zv μ, ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q := by
    have hK : IsPGroup 2 ↥(Zv α ⊔ Zv μ) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab α)).to_le
        (sup_le (Zv_le_Qv hA α) hZμQα)
    exact fun x hx => exists_mul_of_isPGroup_of_vtype_true hA hvα' hK (sup_le hZαα' hZμα')
      le_sup_left hc.not_le x (Subgroup.mem_sup_right hx)
  have hN1 : Zv α' ≤ Subgroup.normalizer ((Zv α ⊔ Zv μ : Subgroup G) : Set G) := fun z hz =>
    mem_normalizer_sup_of_decomp (stab_le_normalizer_Zv hA α (hZα'G hz))
      (Zv_le_centerOf_Qv hA α' hz).2 hdec
  have hN2 : stab α ⊓ stab μ ≤ Subgroup.normalizer ((Zv α ⊔ Zv μ : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer
      (inf_le_left.trans (stab_le_normalizer_Zv hA α))
      (inf_le_right.trans (stab_le_normalizer_Zv hA μ))
  have hstab : Zv α' ⊔ (stab α ⊓ stab μ) = stab α :=
    sup_edge_eq_stab hA hv hβn hμn hμβ.symm (le_inf hZα'G hZα'β) hnle
  have hN : stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv μ : Subgroup G) : Set G) := by
    rw [← hstab]; exact sup_le hN1 hN2
  obtain ⟨g, hg, hgμ⟩ := stab_transitive_on_nbrs hμn hβn
  have hZβ : Zv β = conjSub (g : G) (Zv μ) := by rw [← hgμ, Zv_smul]
  have hZα : conjSub (g : G) (Zv α) = Zv α := by
    rw [← Zv_smul, smul_eq_of_mem_stab hg]
  have hnorm : stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) := by
    have h1 : Zv α ⊔ Zv β = conjSub (g : G) (Zv α ⊔ Zv μ) := by
      rw [conjSub_sup, hZα, hZβ]
    rw [h1, conjSub_normalizer]
    calc stab α = conjSub (g : G) (stab α) := (conjSub_eq_of_mem hg).symm
      _ ≤ _ := conjSub_mono _ hN
  exact hn (h27 hb2 α β hαβ hv hα hnorm)

theorem hss31At_of_hss27 (hA : F53Amalgam H M S) (h27 : Hss27At H M) : Hss31At H M :=
  hss31At_of_hss27S3 hA (Hss27S3At_of_Hss27At h27)

end F53.Stellmacher

end CFSG.Quasithin
