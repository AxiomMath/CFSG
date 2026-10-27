module

public import CFSG.Quasithin.Background.G12Main
public import CFSG.Quasithin.Background.G12Four
public import CFSG.Quasithin.Background.G12FourB

public section

namespace CFSG.Quasithin.G11

theorem g12_1 : G121Stmt := g12_1_of_four g12_four_fact

theorem g12_12 (h : G121Stmt) : G1212Stmt := g12_12_of_four h g12_part_four_fact

theorem g12_12_all : G1212Stmt := g12_12 g12_1

end CFSG.Quasithin.G11
