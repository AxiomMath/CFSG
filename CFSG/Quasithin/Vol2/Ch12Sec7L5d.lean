module

public import CFSG.Quasithin.H13.L32NLem14330a
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch12Sec7Lemmas

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem centralizer_conj (g v : G) :
    Subgroup.centralizer ({g * v * g⁻¹} : Set G) =
      (Subgroup.centralizer ({v} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * v = g⁻¹ * (x * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * x) * g := by rw [hx]
      _ = v * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
      _ = g * (v * y) * g⁻¹ := by rw [hy]
      _ = g * v * g⁻¹ * (g * y * g⁻¹) := by group

theorem map_conj_eq {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
    exact this (by simpa [mul_assoc] using hx)

theorem relIndex_centralizer_conj {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (v : G) :
    (Subgroup.centralizer ({g * v * g⁻¹} : Set G)).relIndex L =
      (Subgroup.centralizer ({v} : Set G)).relIndex L := by
  conv_lhs => rw [centralizer_conj, ← map_conj_eq hg]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

variable [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_map_conj {A X : Subgroup G} (h : IsSylowTwoOf A X) (g : G) :
    IsSylowTwoOf (A.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  have e : ((A.map (MulAut.conj g).toMonoidHom).subgroupOf
      (X.map (MulAut.conj g).toMonoidHom)).index = (A.subgroupOf X).index :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  rw [e]
  exact h.2.2

omit [Finite G] in
theorem isSylowTwoOf_of_ge {P Q H : Subgroup G} (hP : IsSylowTwoOf P H) (hPQ : P ≤ Q)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 ↥Q) : IsSylowTwoOf Q H :=
  ⟨hQH, hQ, fun h2 => hP.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left H hPQ))⟩

theorem hyp1271_conj {T L V : Subgroup G} (h : Hyp1271 G T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {k : G} (hk : k ∈ L) :
    Hyp1271 G (CFSG.conjugate T k⁻¹) L V :=
  ⟨L14328.hyp1223_conj h.hyp hTV hk, h.hatA6⟩

theorem exists_mem_isSylowTwoOf (h1225 : Stmt12_2_5) (h74 : Lemma12_7_4) {T L V : Subgroup G}
    (h : Hyp1271 G T L V) (hTV : T ≤ Subgroup.normalizer (V : Set G)) {t : G} (ht : t ∈ V)
    (ht1 : t ≠ 1) (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) :
    ∃ k ∈ L, IsSylowTwoOf (CFSG.conjugate T k⁻¹ ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hy := h.hyp
  have hTMV : IsSylowTwoOf T hy.MV := by
    refine ⟨le_inf hy.normalizes hTV, hy.sylow.1, fun h2 => hy.sylow.2 ?_⟩
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le (le_inf hy.normalizes hTV))
  obtain ⟨Y, hY⟩ := exists_isSylowTwoOf
    (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
  have hMt : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ hy.MV :=
    (h1225 G T L V hy t ht ht1).2.2.2.2
  obtain ⟨g, hg, hgY⟩ := exists_conj_le_of_isSylowTwoOf hTMV (hY.1.trans hMt) hY.2.1
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := hg.1
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := hg.2
  set t' := g * t * g⁻¹ with ht'
  have ht'V : t' ∈ V := (Subgroup.mem_normalizer_iff.mp hgV t).mp ht
  have hMt' : (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t'} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, centralizer_conj]
    congr 1
    exact map_conj_eq (Subgroup.le_normalizer hgL)
  have hsyl' : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t'} : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t'} : Set G)) := by
    have h1 := isSylowTwoOf_map_conj hY g
    rw [hMt'] at h1
    exact isSylowTwoOf_of_ge h1 (le_inf hgY (h1.1.trans inf_le_right))
      (inf_le_inf_right _ hy.normalizes) (hy.sylow.1.to_le inf_le_left)
  have h18' : (Subgroup.centralizer ({t'} : Set G)).relIndex L = 18 := by
    rw [ht', relIndex_centralizer_conj hgL, h18]
  obtain ⟨⟨z, -, -, -, t₀, -, -, h45, -, horb⟩, -⟩ := h74 G T L V h
  have hto : ∀ v ∈ V, v ≠ 1 → (Subgroup.centralizer ({v} : Set G)).relIndex L = 18 →
      ∃ l ∈ L, l * v * l⁻¹ = t₀ := by
    intro v hv hv1 hv18
    rcases horb v hv hv1 with ⟨l, hl, hlv⟩ | hl
    · exfalso
      have := relIndex_centralizer_conj (Subgroup.le_normalizer hl) v
      rw [hlv, h45, hv18] at this
      norm_num at this
    · exact hl
  have ht'1 : t' ≠ 1 := by
    rw [ht']
    intro h1
    apply ht1
    have e := congrArg (fun x => g⁻¹ * x * g) h1
    simp only [mul_one, inv_mul_cancel] at e
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := e
  obtain ⟨l₁, hl₁, e₁⟩ := hto t ht ht1 h18
  obtain ⟨l₂, hl₂, e₂⟩ := hto t' ht'V ht'1 h18'
  set k := l₁⁻¹ * l₂ with hk
  have hkL : k ∈ L := L.mul_mem (L.inv_mem hl₁) hl₂
  have hkt : k * t' * k⁻¹ = t := by
    rw [hk]
    calc l₁⁻¹ * l₂ * t' * (l₁⁻¹ * l₂)⁻¹ = l₁⁻¹ * (l₂ * t' * l₂⁻¹) * l₁ := by group
      _ = l₁⁻¹ * (l₁ * t * l₁⁻¹) * l₁ := by rw [e₂, e₁]
      _ = t := by group
  refine ⟨k, hkL, ?_⟩
  have h2 := isSylowTwoOf_map_conj hsyl' k
  have hkN : k ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hkL
  have e3 : (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t'} : Set G)).map
      (MulAut.conj k).toMonoidHom =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, ← centralizer_conj, hkt]
    congr 1
    exact map_conj_eq (Subgroup.le_normalizer hkN)
  have e4 : (T ⊓ Subgroup.centralizer ({t'} : Set G)).map (MulAut.conj k).toMonoidHom =
      CFSG.conjugate T k⁻¹ ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, ← centralizer_conj, hkt]
    congr 1
    show _ = T.map (MulAut.conj k⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
  rw [e3, e4] at h2
  exact h2

end CFSG.Quasithin.H13.S127.L5
